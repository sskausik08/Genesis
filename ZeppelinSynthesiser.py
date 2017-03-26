from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import networkx as nx
from subprocess import *
from collections import deque
import math
import gurobipy as gb
import copy
from collections import defaultdict
#import matplotlib.pyplot as plt

class ZeppelinSynthesiser(object) :
	def __init__(self, topology, pdb, backup=False) :
		self.topology = topology
		self.pdb = pdb

		self.fwdmodel = None 
		
		# Route Filters
		self.constraintIndex = 0
		self.DISABLE_ROUTE_FILTERS = True

		# Profiling Information.
		self.z3constraintTime = 0 # Time taken to create the constraints.
		self.z3addTime = 0 # Time taken to add the constraints.
		self.z3numberofadds = 0 # Count of adds.
		self.z3solveTime = 0 # Time taken to solve the constraints. 
		self.metisTime = 0	# Time taken to partition  the graphs.
		self.z3SolveCount = 0	# Count of z3 solve instances. 

		# ILP
		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)

		self.staticRoutes = dict()
		
		self.sums = []
		# Resilience 
		self.SRCount = 0
		self.waypoints = dict()

		# Constants
		self.MAX_GUROBI_ITERATIONS = 600
		self.backupFlag = backup
		self.maximalBackupFlag = False # maximalBackup

		self.inconsistentSRs = 0
		self.sourceSRs = 0
		self.inconsistentBPs = 0

		# Gurobi Constraints
		self.distanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.backupPathConstraints = defaultdict(lambda:defaultdict(lambda:None))

	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 

		dsts = self.pdb.getDestinationSubnets()

		for sw1 in range(1,swCount+1):
			for sw2 in self.topology.getSwitchNeighbours(sw1) :
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=1.00, ub=1000, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + "_")

		self.distSum = 0
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=1, ub=10000, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + "_")
				self.distSum += self.distVars[sw1][sw2][0]
				# for dst in dsts : 
				# 	self.distVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00,vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2)+"-"+str(dst) + " ")

		# self.backupPathVars = defaultdict(lambda:defaultdict(lambda:None))
		# self.bpVarSum = 0
		# for dst in self.backupPaths : 
		# 	backupPaths = self.backupPaths[dst]
		# 	for backupPath in backupPaths : 
		# 		self.backupPathVars[backupPath[0]][dst] = self.ilpSolver.addVar(vtype=gb.GRB.BINARY, name="B-" + str(backupPath[0])+"-"+str(dst) + "_")
		# 		self.bpVarSum += self.backupPathVars[backupPath[0]][dst]
		self.ilpSolver.update()

	def initializeStaticRoutes(self) :
		self.staticRoutes = dict()
		for dst in self.pdb.getDestinationSubnets() :
			self.staticRoutes[dst] = []

		self.staticRoutes[0] = [] # Default destination val = 0 (Not a s)

		# Gurobi Constraints
		self.distanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.waypointResilienceConstraints = defaultdict(lambda:defaultdict(lambda:None))
		self.backupPathConstraints = defaultdict(lambda:defaultdict(lambda:None))
		self.inconsistentSRs = 0
		self.inconsistentBPs = 0

	def initializeEndpointResilience(self) : 
		# Without filters, all sources have maximum resilience = number of source neighbours.
		for endpt in self.endpoints :
			# Get all neighbours at source
			totalres = len(self.topology.getAllSwitchNeighbours(endpt[0]))
			self.endpointResilience[endpt[0]][endpt[1]] = totalres

	def ew(self, sw1, sw2) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if sw2 not in neighbours : 
			raise LookupError("Weight for non-neighbours referred!")
		else : 
			return self.edgeWeights[sw1][sw2]
	
	def rf(self, sw1, sw2, dst) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if sw2 not in neighbours : 
			raise LookupError("Route Filter for non-neighbours referred!")
		else : 
			return self.routefiltersVars[sw1][sw2][dst]

	def dist(self, sw1, sw2, dst=0) : 
		# Default value of dst = 0
		if sw1 == sw2 : 
			return 0.0
		return self.distVars[sw1][sw2][dst]

	def bp(self, sw, dst) : 
		return self.backupPathVars[sw][dst]

	def enforceDAGs(self, dags, endpoints, backups=None, bgpExtensions=None):
		""" Enforce the input destination dags """
		start_t = time.time()
		self.overlay = dict()
		self.destinationDAGs = copy.deepcopy(dags)
		if self.backupFlag : 
			self.backupPaths = copy.deepcopy(backups)
		else : 
			self.backupPaths = dict()
		self.spGraphs = []
		self.bgpExtensions = []
		if bgpExtensions != None : 
			# For an inter-domain setting, there are instances when 
			# a source must have distance to its endpoint smaller 
			# than another endpoint in the topology. 
			# BGPextensions is a list of [src, end1, end2, dst] tuples 
			# which specifies src1 -> end1 path is smaller than src1 -> end2
			self.bgpExtensions = copy.deepcopy(bgpExtensions)

		self.endpoints = copy.deepcopy(endpoints)
		
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()

		# self.f = open('timing', 'a')
		# self.f.write(str(dags))
		# self.f.write("\n\n\n")

		self.constructOverlay()	
		#self.overlayConnectivity()	
		self.disableUnusedEdges()
		self.initializeSMTVariables()
		self.initializeStaticRoutes()

		start_t = time.time()
		self.addDjikstraShortestPathConstraints()

		# Adding constraints without static routes
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag, True)

		# Add constraints for backup paths
		if self.backupFlag : 
			for dst in self.backupPaths : 
				backupPaths = self.backupPaths[dst]
				dag = self.destinationDAGs[dst]
				for backupPath in backupPaths : 
					self.addBackupPathConstraints(dst, dag, backupPath, False) 

		#print "Solving ILP without static routes"
		solvetime = time.time()
		#modelsat = self.z3Solver.check()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime
	
		self.staticRouteMode = False
		status = self.ilpSolver.status

		if status == gb.GRB.INFEASIBLE :
			if self.maximalBackupFlag :
				self.maximalBackup()
				self.topology.enableAllEdges()
				# Extract Edge weights for Gurobi		
				self.getEdgeWeightModel(self.staticRouteMode)	
				self.pdb.validateControlPlane(self.topology, self.staticRoutes, self.backupPaths)

			else : 
				#print "solving ILP with static routes"
				self.staticRouteMode = True

				#self.findValidCycles()
				self.ilpSolver = gb.Model("C3")
				self.ilpSolver.setParam('OutputFlag', 0)
				self.initializeSMTVariables()
				self.initializeStaticRoutes()
				self.addDjikstraShortestPathConstraints()

				# Prompted by Gurobi? 
				# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
				# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 
				start1 = time.time()
				# Adding constraints with routeFilter variables at source
				for dst in dsts : 
					dag = self.destinationDAGs[dst]
					self.addDestinationDAGConstraints(dst, dag)

				if self.backupFlag : 
					for dst in self.backupPaths : 
						backupPaths = self.backupPaths[dst]
						dag = self.destinationDAGs[dst]
						for backupPath in backupPaths : 
							self.addBackupPathConstraints(dst, dag, backupPath, True) 

				self.enforceResilience()

				solvetime = time.time()
				self.ilpSolver.optimize()
				self.z3solveTime += time.time() - solvetime

				status = self.ilpSolver.status

				while status == gb.GRB.INFEASIBLE or status == gb.GRB.INF_OR_UNBD  :
					# Perform inconsistency analysis using Gurobi
					attempts = 1
					self.ilpSolver.computeIIS()
					self.repairInconsistency()
					
					solvetime = time.time()
					self.ilpSolver.optimize()
					self.z3solveTime += time.time() - solvetime

					status = self.ilpSolver.status
				
		# Extract Edge weights from Gurobi		
		self.getEdgeWeightModel(self.staticRouteMode)	
		
		# Add static routes to ensure there arent any violations
		self.removeViolations()
		# self.f.close()	
		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.staticRoutes, self.backupPaths)
		self.pdb.validateControlPlaneResilience(self.topology, self.staticRoutes, self.waypoints)

		srCount = 0
		# Translate route filters to switch names
		self.staticRouteNames = dict()
		for subnet in self.staticRoutes.keys() :
			srs = self.staticRoutes[subnet]
			srCount += len(srs)
			srNames = []
			for sr in srs : 
				srNames.append([self.topology.getSwName(sr[0]), self.topology.getSwName(sr[1])])
			self.staticRouteNames[subnet] = srNames

		
		# self.zepFile = open("ospf-timing", 'a')
		# self.zepFile.write("Topology Switches\t" +  str(swCount))
		# self.zepFile.write("\n")
		print "Time1" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(time.time() - start_t)
		# self.zepFile.write("Time" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(time.time() - start_t))
		# self.zepFile.write("\n")
		# self.zepFile.write("Static Routes" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(srCount) + "\t")
		# self.zepFile.write("\n")

		exit(0)
		#return self.staticRouteNames


	# def synthesizeRepair(self) :
	# 	# Consider the repair problem now. #Experimental code
	# 	oldDags = copy.deepcopy(self.destinationDAGs)

	# 	changeCount = 4
	# 	random.shuffle(dsts)
	# 	for changedDst in dsts : 
	# 		newDag = self.changeDag(self.destinationDAGs[changedDst])
	# 		if newDag != self.destinationDAGs[changedDst] : 
	# 			self.destinationDAGs[changedDst] = newDag 
	# 			self.pdb.addDestinationDAG(changedDst, newDag)
	# 			changeCount = changeCount - 1

	# 		if changeCount == 0 : 
	# 			break

	# 	if changeCount > 0 : 
	# 		print "Wait, what?"
	# 		exit(0)
		
	# 	self.repair(oldDags, self.destinationDAGs, self.edgeWeightValues)

		


	# def changeDag(self, dag) :
	# 	newDag = copy.deepcopy(dag)

	# 	for sw in newDag : 
	# 		if newDag[sw] == None :
	# 			dstSw = sw
		
	# 	newpath = []
	# 	for sw in newDag :
	# 		if sw != dstSw :
	# 			paths = self.topology.getAllPaths(sw, dstSw)
	# 			if len(paths) <= 1 :
	# 				continue
	# 			for path in paths : 
	# 				# Check if path creates a loop. 
	# 				loopedPath = False
	# 				for i in range(1, len(path) - 1) :  
	# 					loopedPath = False
	# 					if path[i] in newDag : 
	# 						nextsw = path[i] 
	# 						while nextsw != None : 
	# 							if nextsw == sw : 
	# 								# This path loops back to sw. Dont use
	# 								loopedPath = True
	# 								break
	# 							nextsw = newDag[nextsw]

	# 					if loopedPath : 
	# 						break
	# 				if loopedPath : 
	# 					continue

	# 				newpath = [sw]
	# 				# Choose this path
	# 				for i in range(1, len(path)) :
	# 					if path[i] not in newDag : 
	# 						newpath.append(path[i])
	# 					else :
	# 						newpath.append(path[i])
	# 						break
	# 			if len(newpath) > 0 : 
	# 				break
	# 		if len(newpath) > 0 : 
	# 			break			

	# 	for i in range(0, len(newpath) - 1) :
	# 		newDag[newpath[i]] = newpath[i + 1]

	# 	return newDag
	"""
	An IIS is a subset of the constraints and variable bounds of the original model. 
	If all constraints in the model except those in the IIS are removed, the model is still infeasible. 
	However, further removing any one member of the IIS produces a feasible result.
	"""	
	def repairInconsistency(self) :
		""" Pick static routes/ remove backup paths greedily """
		staticRoutes = []
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "SR" :
					# Static Route constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [int(fields[1]), int(fields[2]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[4])] : 
							# Compute score for static route
							staticRoutes.append([[int(fields[1]), int(fields[2]), int(fields[4])], 1])

		waypointPaths = []
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "WD" :
					# backup path constraint
					foundFlag = False
					for index in range(len(waypointPaths)) :
						if waypointPaths[index][0] == [int(fields[1]), int(fields[2])] : 
							waypointPaths[index] = [waypointPaths[index][0], waypointPaths[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						waypointPaths.append([[int(fields[1]), int(fields[2])], 1])

		if len(staticRoutes) == 0 and len(waypointPaths) == 0: 
			print "INFEASIBLE forever, should never ever ever happen at all!"

			for constr in self.ilpSolver.getConstrs() :
				if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
					print constr 

			exit(0)

		if len(staticRoutes) > 0 : 
			# Check if there is a static route leadint to dstSw
			for sr in staticRoutes : 
				dag = self.destinationDAGs[sr[0][2]]
				for sw in dag :
					if dag[sw] == None : 
						dstSw = sw
				if dstSw == sr[0][1] :
					# Pick this static route! 
					self.addStaticRoute(sr[0][0], sr[0][1], sr[0][2])
					#print "Picked the static route at dst switch!"
					return

			# Check if a static route starts at a switch with no backup paths
			for sr in staticRoutes : 
				sw1 = sr[0][0]
				dag = self.destinationDAGs[sr[0][2]]
				for sw in dag :
					if dag[sw] == None : 
						dstSw = sw
				mincut = self.topology.findMinCut(sw1, dstSw)
				if mincut == 1 : 
					# No backup path at sw1. Pick this static route.
					self.addStaticRoute(sr[0][0], sr[0][1], sr[0][2])
					#print "Picked the static route at switch with no backup paths!"
					return

			# Check if a static route ends at a switch with no back up paths'
			nonResilientStaticRoutes = []
			for sr in staticRoutes : 
				sw2 = sr[0][1]
				dag = self.destinationDAGs[sr[0][2]]
				for sw in dag :
					if dag[sw] == None : 
						dstSw = sw
				mincut = self.topology.findMinCut(sw2, dstSw)
				if mincut == 1 : 
					nonResilientStaticRoutes.append(sr)

			if len(nonResilientStaticRoutes) == len(staticRoutes) :
				print "No option than to lose some resilience!"
			else :
				# Choose from resilient filters. 
				for sr in nonResilientStaticRoutes :
					staticRoutes.remove(sr)

			# Check if a static route is at the source. Try to remove those.
			# sourceStaticRoutes = []
			# for sr in staticRoutes : 
			# 	sw1 = sr[0][0]
			# 	dst = sr[0][2]
			# 	if [sw1, dst] in self.endpoints : 
			# 		# Source SR
			# 		sourceStaticRoutes.append(sr)
			
			# if len(sourceStaticRoutes) == len(staticRoutes) :
			# 	self.sourceSRs += 1
			# 	print "No option than to add static routes at source", self.sourceSRs
				
			# else :
			# 	# Choose from resilient filters. 
			# 	for sr in sourceStaticRoutes :
			# 		staticRoutes.remove(sr)


			sr = None
			count = 0
			for ind in range(len(staticRoutes)) : 
				if staticRoutes[ind][1] > count : 
					sr = staticRoutes[ind][0]
					count = staticRoutes[ind][1]

			# Pick the best static Route
			self.addStaticRoute(sr[0], sr[1], sr[2])

		elif len(waypointPaths) > 0 : 
			bp = None
			count = 0
			for ind in range(len(waypointPaths)) : 
				if waypointPaths[ind][1] > count : 
					bp = waypointPaths[ind][0]
					count = waypointPaths[ind][1]

			# Pick the best static Route
			self.removeWaypointPath(bp[0], bp[1])

	def removeViolations(self) : 
		self.staticRoutesAdded = 0
		for pc in range(self.pdb.getPacketClassRange()) :
			srcSw = self.pdb.getSourceSwitch(pc)
			dstSw = self.pdb.getDestinationSwitch(pc)
			dst = self.pdb.getDestinationSubnet(pc)
			dag = self.destinationDAGs[dst]
			gpath = []
			nextsw = srcSw
			while nextsw != dstSw : 
				path = self.topology.getShortestPath(nextsw, dstSw)
				if path[1] != dag[nextsw] and [nextsw, dag[nextsw]] not in self.staticRoutes[dst] : 
					# Add a static route to remove violation
					self.staticRoutes[dst].append([nextsw, dag[nextsw]])

					self.staticRoutesAdded += 1
				nextsw = dag[nextsw]

		print "Added static routes is ", self.staticRoutesAdded

	def constructOverlay(self) :
		dsts = self.pdb.getDestinationSubnets()
		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			self.overlay[sw] = self.topology.getSwitchNeighbours(sw)

		# for dst in dsts : 
		# 	dag = self.destinationDAGs[dst]
		# 	for sw1 in dag :
		# 		sw2 = dag[sw1] # Edge sw1 -> sw2
		# 		if sw2 != None : 
		# 			if sw2 not in self.overlay[sw1] : 
		# 				self.overlay[sw1].append(sw2)

	def disableUnusedEdges(self) : 
		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			neighbours = self.topology.getSwitchNeighbours(sw)
			if sw in self.overlay :
				activeNeighbours = self.overlay[sw]
				for n in neighbours :
					if n not in activeNeighbours : 
						self.topology.disableEdge(sw, n)
			else :
				# All edges are disabled
				for n in neighbours : 
					self.topology.disableEdge(sw, n)

	def overlayConnectivity(self) :
		""" Construct  connectivity in overlay graph"""
		swCount = self.topology.getSwitchCount()
		self.connectivity = [[False for x in range(swCount + 1)] for x in range(swCount + 1)]
		for sw in self.overlay : 
			self.connectivity[sw][sw] = True
			for n in self.overlay[sw] : 
				self.connectivity[sw][n] = True
		
		explored = dict()
		for sw in self.overlay : 
			explored[sw] = False

		for sw in self.overlay : 
			print "exploring ", sw
			# Do a BFS to explore connectivity
			swQueue1 = [sw]
			swQueue2 = []
			visited = dict()
			for sw1 in  self.overlay : 
				visited[sw1] = False
			while len(swQueue1) > 0 : 
				for sw1 in swQueue1 :
					visited[sw1] = True
					self.connectivity[sw][sw1] = True
					for n in self.overlay[sw1] : 
						self.connectivity[sw][n] = True
						if explored[n] : 
							# n has been explored. Dont need to do bfs along n. Set connectivity for all n
							for sw2 in self.overlay : 
								if self.connectivity[n][sw2] : 
									self.connectivity[sw][sw2] = True
						elif not visited[n]: 
							swQueue2.append(n)
				swQueue1 = swQueue2
				swQueue2 = []
			explored[sw] = True

	# These constraints are solved fast.
	def addDjikstraShortestPathConstraints(self) :
		swCount = self.topology.getSwitchCount()

		for s in range(1, swCount + 1):
			if self.topology.isSwitchDisabled(s) :
				continue
			for t in range(1, swCount + 1) :
				if self.topology.isSwitchDisabled(t) :
					continue
				if s == t : 
					continue

				for sw in self.topology.getSwitchNeighbours(s) :
					self.ilpSolver.addConstr(self.dist(s, t) <= self.ew(s, sw) + self.dist(sw, t), "D-" + str(self.constraintIndex) + " ")	
					self.constraintIndex += 1


	def addDestinationDAGConstraints(self, dst, dag, staticRouteMode=True) :
		""" Adds constraints such that dag weights are what we want them to be with static routing disabled/enabled """	
		for sw in dag : 
			if self.distanceConstraints[sw][dag[sw]][dst] == None : 
				self.distanceConstraints[sw][dag[sw]][dst] = []
		
			t = dag[sw]
			while t != None :				
				distconstr = self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, dag[sw]) + self.dist(dag[sw], t), 
					"SR-" + str(sw) + "-" + str(dag[sw]) + "-" + str(t) + "-" + str(dst) + "-" + str(self.constraintIndex))
				
				self.distanceConstraints[sw][dag[sw]][dst].append(distconstr)
				self.constraintIndex += 1
				
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n != dag[sw] : 
						distconstr = self.ilpSolver.addConstr(self.dist(sw, t) <= self.ew(sw, n) + self.dist(n, t) - 1, 
							"SR-" + str(sw) + "-" + str(dag[sw]) + "-" + str(t) + "-" + str(dst) + "-" + str(self.constraintIndex))
						
						self.distanceConstraints[sw][dag[sw]][dst].append(distconstr)
						self.constraintIndex += 1

				t = dag[t]

		self.addBGPExtensionConstraints(dst, dag, staticRouteMode)

	def addBackupPathConstraints(self, dst, dag, backupPath, staticRouteMode) :
		""" Adds constraints such backup path is activated when the main path fails"""	
		for sw in dag :
			if dag[sw] == None :
				dstSw = sw

		startSw = backupPath[0]
		origSw = dag[startSw]
		backupSw = backupPath[1]

		# Ensure backup path is shorter than the other switches at startSw
		backupDist = 0
		for i in range(len(backupPath) - 1) : 
			backupDist += self.ew(backupPath[i], backupPath[i + 1])

		self.backupPathConstraints[backupPath[0]][dst] = []
		neighbours = self.topology.getSwitchNeighbours(startSw)
		for n in neighbours : 
			if n != origSw and n != backupSw :
				constr = self.ilpSolver.addConstr(backupDist  
					<= self.ew(startSw, n) + self.dist(n, dstSw) - 1, 
					"BP-" + str(backupPath[0]) + "-" + str(dst) + "-" + str(self.constraintIndex))
				self.backupPathConstraints[backupPath[0]][dst].append(constr)
				self.constraintIndex += 1


		origDist = self.ew(startSw, origSw)
		while origSw != dstSw : 
			# Ensure backup path is shorter than the other paths starting at origSw
			neighbours = self.topology.getSwitchNeighbours(origSw)
			for n in neighbours : 
				if n != dag[origSw] : 
					constr = self.ilpSolver.addConstr(backupDist 
						<= origDist + self.ew(origSw, n) + self.dist(n, dstSw) - 1, 
						"BP-" + str(backupPath[0]) + "-" + str(dst) + "-" + str(self.constraintIndex))
					self.backupPathConstraints[backupPath[0]][dst].append(constr)
					self.constraintIndex += 1

			origDist += self.ew(origSw, dag[origSw])
			origSw = dag[origSw]

		# Create a dag from backupSw to dstSw and add shortest path constraints
		backupDag = dict()
		for i in range(1, len(backupPath) - 1):
			backupDag[backupPath[i]] = backupPath[i + 1]
		backupDag[dstSw] = None

		if not staticRouteMode :
			for sw in backupDag : 
				t = backupDag[sw]
				while t != None :				
					constr = self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, backupDag[sw]) + self.dist(backupDag[sw], t))
					self.backupPathConstraints[backupPath[0]][dst].append(constr)

					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n != backupDag[sw] : 
							constr = self.ilpSolver.addConstr(self.dist(sw, t) <= self.ew(sw, n) + self.dist(n, t) - 1)
							self.backupPathConstraints[backupPath[0]][dst].append(constr)

					t = backupDag[t]
		else:
			for sw in backupDag :	
				if sw == dstSw : continue					
				nextsw = sw
				totalDist = 0 # Store the distance from sw to t along backupDag.
				while nextsw != dstSw : 
					totalDist += self.ew(nextsw, backupDag[nextsw])
					nextsw = backupDag[nextsw]

				constr = self.ilpSolver.addConstr(self.dist(sw, dstSw) <= totalDist)
				self.backupPathConstraints[backupPath[0]][dst].append(constr)

				if not [sw, backupDag[sw]] in self.staticRoutes[dst] : 
					neighbours = self.topology.getSwitchNeighbours(sw)
					if self.distanceConstraints[sw][backupDag[sw]][dst] == None : 
						self.distanceConstraints[sw][backupDag[sw]][dst] = []
					for n in neighbours : 
						if n != backupDag[sw]: 
							distconstr = self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, dstSw) - 1, 
							"SR-" + str(sw) + "-"+ str(backupDag[sw]) + "-" + str(dstSw) + "-" + str(dst) + "-" + str(self.constraintIndex))

							self.distanceConstraints[sw][backupDag[sw]][dst].append(distconstr)
							self.constraintIndex += 1


	def addMaximalBackupPathConstraints(self, dst, dag, backupPath, staticRouteMode) :
		""" Adds constraints such backup path is activated when the main path fails"""	
		for sw in dag :
			if dag[sw] == None :
				dstSw = sw

		startSw = backupPath[0]
		origSw = dag[startSw]
		backupSw = backupPath[1]

		bpVar = self.bp(backupPath[0], dst)

		# Ensure backup path is shorter than the other switches at startSw
		backupDist = 0
		for i in range(len(backupPath) - 1) : 
			backupDist += self.ew(backupPath[i], backupPath[i + 1])

		self.backupPathConstraints[backupPath[0]][dst] = []
		neighbours = self.topology.getSwitchNeighbours(startSw)
		for n in neighbours : 
			if n != origSw and n != backupSw :
				constr = self.ilpSolver.addConstr(backupDist  
					<= self.ew(startSw, n) + self.dist(n, dstSw) - 1 + 1000000 * bpVar, 
					"BP-" + str(backupPath[0]) + "-" + str(dst) + "-" + str(self.constraintIndex))

				self.constraintIndex += 1


		origDist = self.ew(startSw, origSw)
		while origSw != dstSw : 
			# Ensure backup path is shorter than the other paths starting at origSw
			neighbours = self.topology.getSwitchNeighbours(origSw)
			for n in neighbours : 
				if n != dag[origSw] : 
					constr = self.ilpSolver.addConstr(backupDist 
						<= origDist + self.ew(origSw, n) + self.dist(n, dstSw) - 1 + 1000000 * bpVar, 
						"BP-" + str(backupPath[0]) + "-" + str(dst) + "-" + str(self.constraintIndex))
	
					self.constraintIndex += 1

			origDist += self.ew(origSw, dag[origSw])
			origSw = dag[origSw]

		# Create a dag from backupSw to dstSw and add shortest path constraints
		backupDag = dict()
		for i in range(1, len(backupPath) - 1):
			backupDag[backupPath[i]] = backupPath[i + 1]
		backupDag[dstSw] = None

		if not staticRouteMode :
			for sw in backupDag : 
				t = backupDag[sw]
				while t != None :				
					constr = self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, backupDag[sw]) + self.dist(backupDag[sw], t))
	
					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n != backupDag[sw] : 
							constr = self.ilpSolver.addConstr(self.dist(sw, t) <= self.ew(sw, n) + self.dist(n, t) - 1)
			

					t = backupDag[t]
		else:
			for sw in backupDag :	
				if sw == dstSw : continue					
				nextsw = sw
				totalDist = 0 # Store the distance from sw to t along backupDag.
				while nextsw != dstSw : 
					totalDist += self.ew(nextsw, backupDag[nextsw])
					nextsw = backupDag[nextsw]

				constr = self.ilpSolver.addConstr(self.dist(sw, dstSw) <= totalDist)


				if not [sw, backupDag[sw]] in self.staticRoutes[dst] : 
					neighbours = self.topology.getSwitchNeighbours(sw)
					if self.distanceConstraints[sw][backupDag[sw]][dst] == None : 
						self.distanceConstraints[sw][backupDag[sw]][dst] = []
					for n in neighbours : 
						if n != backupDag[sw]: 
							distconstr = self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, dstSw) - 1, 
							"SR-" + str(sw) + "-"+ str(backupDag[sw]) + "-" + str(dstSw) + "-" + str(dst) + "-" + str(self.constraintIndex))

							self.distanceConstraints[sw][backupDag[sw]][dst].append(distconstr)
							self.constraintIndex += 1

	def addMaximalBackupObjective(self) : 
		self.ilpSolver.setObjective(self.bpVarSum, gb.GRB.MINIMIZE)
		self.ilpSolver.update()

	def maximalBackup(self) : 
		print "Solving maximal backup"
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()
		
		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)
		self.initializeSMTVariables()
		self.initializeStaticRoutes()

		self.addDjikstraShortestPathConstraints()

		# Prompted by Gurobi? 
		# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
		# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 

		# Adding constraints 
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag)

		for dst in self.backupPaths : 
			backupPaths = self.backupPaths[dst]
			dag = self.destinationDAGs[dst]
			for backupPath in backupPaths : 
				self.addMaximalBackupPathConstraints(dst, dag, backupPath, True) 

		self.addMaximalBackupObjective()

		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime

		status = self.ilpSolver.status

		while status == gb.GRB.INFEASIBLE :
			# Perform inconsistency analysis using Gurobi
			attempts = 1
			self.ilpSolver.computeIIS()
			self.repairInconsistency()
			
			solvetime = time.time()
			self.ilpSolver.optimize()
			self.z3solveTime += time.time() - solvetime

			status = self.ilpSolver.status

	def addBGPExtensionConstraints(self, dst, dag, staticRouteMode=True) :
		# TODO: Change wrt static routes
		for tup in self.bgpExtensions: 
			if tup[3] != dst : continue
			src = tup[0]
			end1 = tup[1]
			end2 = tup[2]
			if not staticRouteMode :
				while src != None:
					self.ilpSolver.addConstr(self.dist(src, end1) <= self.dist(src, end2) - 1)
					src = dag[src]
			else:
				while src != end1:			
					nextsw = src
					totalDist = 0 # Store the distance from sw to end1 along dag.
					while nextsw != end1 : 
						totalDist += self.ew(nextsw, dag[nextsw])
						nextsw = dag[nextsw]

					if not [src, dag[src]] in self.staticRoutes[dst] : 
						neighbours = self.topology.getSwitchNeighbours(src)
						for n in neighbours : 
							if n != dag[src] : 
								self.ilpSolver.addConstr(totalDist <= self.ew(src, n) + self.dist(n, end2) - 1, "SR-" + str(src) + "-" 
									+ str(dag[src]) + "-" + str(end2) + "-" + str(dst) + "-" + str(self.constraintIndex))
								self.constraintIndex += 1
					
					src = dag[src]
					

	def addDestinationDAGConstraintsRF(self, dst, dag) :
		""" Adds constraints such that dag weights are what we want them to be with route filtering disabled/enabled """
		
		for sw in dag : 
			t = dag[sw]
			while t != None :			
				nextsw = sw
				totalDist = 0 # Store the distance from sw to t along dag.
				while nextsw != t : 
					totalDist += self.ew(nextsw, dag[nextsw])
					nextsw = dag[nextsw]

				self.ilpSolver.addConstr(self.dist(sw, t) <= totalDist)

				# Route filtering equations
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n != dag[sw] : 
						self.ilpSolver.addConstr(totalDist <= 10*self.rf(sw,n,dst) + self.ew(sw, n) + self.dist(n, t) - 1, "C-" + str(dst) + "-" + str(self.constraintIndex))
						self.constraintIndex += 1
				
				t = dag[t]			

	def addMinimalFilterObjective(self) : 
		totalRouteFilters = 0
		dsts = self.pdb.getDestinationSubnets()
		for dst in dsts:
			dag = self.destinationDAGs[dst]
			for sw1 in dag : 
				for sw2 in self.topology.getSwitchNeighbours(sw1) : 
					if sw2 == dag[sw1] : continue
					else : totalRouteFilters += self.rf(sw1,sw2,dst)

		self.ilpSolver.setObjective(totalRouteFilters, gb.GRB.MINIMIZE)

	def addStaticRoute(self, sw1, sw2, dst) :
		""" Add rf at sw1 -> sw2 for dst """
		if [sw1, sw2] not in self.staticRoutes[dst] :
			self.staticRoutes[dst].append([sw1, sw2]) 
			self.inconsistentSRs += 1

		# Delete distance constraints from model
		distconstrs = self.distanceConstraints[sw1][sw2][dst]
		#print "SR", sw1, sw2, dst
		for dconstr in distconstrs : 
			self.ilpSolver.remove(dconstr)

		self.ilpSolver.update()
	
	def removeBackupPath(self, src, dst) :
		for backupPath in self.backupPaths[dst] :
			if src == backupPath[0] :
				# Backup path exists. Remove constraints from model
				print "Removing backupPath", backupPath, dst
				backupConstrs = self.backupPathConstraints[src][dst]
				if backupConstrs == None : continue
				for bpconstr in backupConstrs : 
					self.ilpSolver.remove(bpconstr)

				self.ilpSolver.update()
				
				self.backupPaths[dst].remove(backupPath)
				self.inconsistentBPs += 1
				return

	def removeWaypointPath(self, sw, dst) :
		""" Remove the waypoint resilient path"""
		#print "Removing waypoint path at", sw, dst
		waypointConstrs = self.waypointResilienceConstraints[sw][dst]
		if waypointConstrs == None : return
		for wconstr in waypointConstrs : 
			self.ilpSolver.remove(wconstr)

		self.ilpSolver.update()
		return

	def getEdgeWeightModel(self, staticRouteMode=True) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()
		# self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

		self.edgeWeightValues = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) : 
				if n not in self.overlay[sw] :
					self.topology.addWeight(sw, n, float(100000))
					self.edgeWeightValues[sw][n] = float(100000)
					#print sw, n, 1000
				else : 
				# ew_rat = self.fwdmodel.evaluate(self.ew(sw,n))
				# self.topology.addWeight(sw, n, float(ew_rat.numerator_as_long())/float(ew_rat.denominator_as_long()))
					ew = self.ew(sw, n).x
					# if [sw,n] in self.hiddenEdges : 
					# 	ew = 1000
					self.topology.addWeight(sw, n, float(ew))
					self.edgeWeightValues[sw][n] = float(ew)
					#print "EW ", sw, n,  float(ew)

		dst = self.pdb.getDestinationSubnet(0)
		for sw1 in range(1, swCount + 1) :
			for sw2 in range(1, swCount + 1) :
				if sw1 == sw2 : continue

				dist = self.dist(sw1, sw2).x
				wdist = self.wdist(sw1, sw2, dst).x
				
				#print "D ", sw1, sw2, dist, wdist

		if not staticRouteMode :
			# Route filters not used. 
			return 

		totalStaticRoutes = 0
		setStaticRoutes = 0
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			totalStaticRoutes += len(dag) - 1 

			if dst in self.backupPaths : 
				backupPaths = self.backupPaths[dst]
				for backupPath in backupPaths : 
					totalStaticRoutes += len(backupPath) - 2  # Cant have a SR on first hop
		
		self.edges = []	
		for dst in dsts : 
			setStaticRoutes += len(self.staticRoutes[dst])
			for sr in self.staticRoutes[dst] :
				if sr not in self.edges : 
					self.edges.append(sr)

		totEdges = 0
		for sw in range(1, swCount + 1) :
			totEdges += len(self.topology.getSwitchNeighbours(sw))

		self.SRCount = setStaticRoutes
		print "Ratio of Static Routes : ", setStaticRoutes, totalStaticRoutes 
		#print "Edges used", len(self.edges), totEdges

		if self.maximalBackupFlag : 
			for dst in self.backupPaths : 
				backupPaths = self.backupPaths[dst]
				for backupPath in backupPaths : 
					bp = self.backupPathVars[backupPath[0]][dst].x
					if bp == 1 : 
						# Backup path not enforced. 
						self.removeBackupPath(backupPath[0], dst)

		totalBackupPaths = 0
		for dst in self.backupPaths : 
			totalBackupPaths += len(self.backupPaths[dst])

		print "Ratio of backup paths : ", totalBackupPaths - self.inconsistentBPs, totalBackupPaths


	# Profiling Statistics : 
	def printProfilingStats(self) :
		#print "Time taken to add constraints are ", self.z3addTime
		print "Zeppelin: Time taken to solve constraints are ", self.z3solveTime
		# print "Number of z3 adds to the solver are ", self.z3numberofadds

	# Backup Functions

	def initializeBackupVariables(self, dst, path, waypoints) : 
		swCount = self.topology.getSwitchCount()
		#self.backupDistVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
	
		# for sw1 in range(1,swCount+1):
		# 	for sw2 in range(1, swCount + 1) :
		# 		for index in range(len(path) - 1): 
		# 			l1 = path[index]
		# 			l2 = path[index + 1]
		# 			if l1 > l2 :
		# 				l = str(l2) + "-" + str(l1)
		# 			else : 
		# 				l = str(l1) + "-" + str(l2)

		# 			self.backupDistVars[sw1][sw2][l] = self.ilpSolver.addVar(lb=1.00, vtype=gb.GRB.CONTINUOUS, 
		# 				name="BD-" + str(sw1)+"-"+str(sw2) + "-" + l + "_")

		self.ilpSolver.update()

		self.waypointDistVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				self.waypointDistVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=1.00, vtype=gb.GRB.CONTINUOUS, 
					name="WD-" + str(sw1)+"-"+str(sw2) + "-" + str(dst) + "_")

		self.ilpSolver.update()

	def bdist(self, sw1, sw2, l) : 
		if sw1 == sw2 : 
			return 0.0
		return self.backupDistVars[sw1][sw2][l]

	def wdist(self, sw1, sw2, dst) : 
		if sw1 == sw2 : 
			return 0.0
		return self.waypointDistVars[sw1][sw2][dst]

	def addBackupDjikstraShortestPathConstraints(self, l1, l2) :
		swCount = self.topology.getSwitchCount()

		if l1 > l2 :
			l = str(l2) + "-" + str(l1)
		else : 
			l = str(l1) + "-" + str(l2)

		for s in range(1, swCount + 1):
			if self.topology.isSwitchDisabled(s) :
				continue
			for t in range(1, swCount + 1) :
				if self.topology.isSwitchDisabled(t) :
					continue
				if s == t : 
					continue

				for sw in self.topology.getSwitchNeighbours(s) :
					if s == l1 and sw == l2 : continue
					if s == l2 and sw == l1 : continue
					self.ilpSolver.addConstr(self.bdist(s, t, l) <= self.ew(s, sw) + self.bdist(sw, t, l), "BD-" + str(self.constraintIndex) + " ")	
					self.constraintIndex += 1

				self.ilpSolver.addConstr(self.bdist(s, t, l) >= self.dist(s, t), "BD-" + str(self.constraintIndex) + " ")	
				self.constraintIndex += 1

	def addWaypointDjikstraShortestPathConstraints(self, dst, waypoints) :
		swCount = self.topology.getSwitchCount()

		for s in range(1, swCount + 1):
			if self.topology.isSwitchDisabled(s) or s in waypoints:
				continue
			for t in range(1, swCount + 1) :
				if self.topology.isSwitchDisabled(t) or t in waypoints:
					continue
				if s == t : 
					continue

				for sw in self.topology.getSwitchNeighbours(s) :
					if sw in waypoints : continue
					self.ilpSolver.addConstr(self. wdist(s, t, dst) <= self.ew(s, sw) + self. wdist(sw, t, dst), 
						"D-" + str(s) + "-" + str(t) + "-" + str(sw) + "_")	
					self.constraintIndex += 1

				self.ilpSolver.addConstr(self. wdist(s, t, dst) >= self.dist(s, t), "D-" + str(self.constraintIndex) + " ")	
				self.constraintIndex += 1

	def addWaypointResilienceConstraints(self, dst, dag, waypoint) : 
		# Add constraints to ensure path after one link failure goes through atleast one waypoint.
		for sw in dag : 
			if dag[sw] == None : 
				dstSw = sw
				break	

		#print dstSw, dag
		# Ensure backup paths dont go come back to the dag.
		for sw in dag : 
			if sw == dstSw : continue 

			disabledEdges = []
			for sw1 in dag :
				neighbours = self.topology.getSwitchNeighbours(sw1)
				for n in neighbours : 
					disabledEdges.append([n, sw1])
			
			path2Waypoint = self.topology.getBFSPath(sw, waypoint, disabledEdges)
			# Path to waypoint does not exist. 
			if path2Waypoint == [] : continue

			# Disable all upstream edges of sw
			upstreamEdges = []
			for sw1 in dag : 
				sw2 = sw1
				while sw2 != None:
					if sw2 == sw : # sw1 is a downstream switch. Disable edges into sw1
						neighbours = self.topology.getSwitchNeighbours(sw2)
						for n in neighbours : 
							upstreamEdges.append([n, sw2])
						break
					sw2 = dag[sw2]

			# Disable all edges coming to path2Waypoint switches
			for sw1 in path2Waypoint : 
				neighbours = self.topology.getSwitchNeighbours(sw1)
				for n in neighbours : 
					upstreamEdges.append([n, sw1])

			path2Dst = self.topology.getBFSPath(waypoint, dstSw, upstreamEdges)
			# Path to dst from waypoint does not exist. 
			if path2Dst == [] : continue

			for sw1 in path2Dst : 
				if sw1 in dag : 
					t = sw1 
					break

			pathDist = 0
			for index in range(len(path2Waypoint) - 1) :
				pathDist += self.ew(path2Waypoint[index], path2Waypoint[index+1])

			for index in range(len(path2Dst) - 1) :
				if path2Dst[index] == t : 
					while t != dstSw : 
						pathDist += self.ew(t, dag[t])
						t = dag[t]
					break
				pathDist += self.ew(path2Dst[index], path2Dst[index+1])

			#print sw, dstSw, waypoint, path2Waypoint, path2Dst
			# Path distance must be smaller than non waypoint distance
			wconstr = self.ilpSolver.addConstr(pathDist <= self.wdist(sw, dstSw, dst) - 1, 
				"WD-" + str(sw) + "-" + str(dst))

			if self.waypointResilienceConstraints[sw][dst] == None : 
				self.waypointResilienceConstraints[sw][dst] = []
			self.waypointResilienceConstraints[sw][dst].append(wconstr)

	def enforceResilience(self) : 
		swCount = self.topology.getSwitchCount()
		pc = 0
		dst = self.pdb.getDestinationSubnet(pc)
		path = self.pdb.getPath(pc)
		dag = self.destinationDAGs[dst]

		while True:
			waypoint = random.randint(1, swCount)
			if waypoint not in dag : 
				break

		waypoints = [waypoint, path[int((len(path) - 1)/2)]]

		self.waypoints[dst] = waypoints
		self.initializeBackupVariables(dst, path, waypoints) 

		self.addWaypointDjikstraShortestPathConstraints(dst, waypoints)

		self.addWaypointResilienceConstraints(dst, dag, waypoint)
	
		# Repair Functions

	def repair(self, oldDags, newDags, edgeWeights) :
		""" Synthesize a new set of configurations inducing newDags such that
		the overhead of change from oldDags is minimized"""
		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)

		# Find affected Switches by the change
		affectedSwitches = self.affectedSwitches(oldDags, newDags)
		print "Number of affected Switches", len(affectedSwitches)

		self.removeInvalidStaticRoutes(newDags)

		self.constructOverlay()	
		#self.overlayConnectivity()	
		self.disableUnusedEdges()
		self.initializeRepairVariables(edgeWeights, affectedSwitches)

		self.addDjikstraShortestPathConstraints()

		dsts = self.pdb.getDestinationSubnets()
		# Adding constraints with static routes enabled
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw in dag : 
				if sw in affectedSwitches : 
					self.addDestinationDAGConstraints(dst, dag)
					break

		print "Here and solving"
		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime

		status = self.ilpSolver.status

		print "Solved repair"

		if status == gb.GRB.INFEASIBLE :
			# Perform inconsistency analysis using Gurobi
			attempts = 1
			inconsistencyVal = self.findRepairInconsistency(edgeWeights, affectedSwitches)
			while inconsistencyVal:
				inconsistencyVal = self.findRepairInconsistency(edgeWeights, affectedSwitches)
				attempts += 1
				if attempts > self.MAX_GUROBI_ITERATIONS :
					break
			#print "inconsistency attempts", attempts
			#print "diamond loss", diamondLoss

		print "Time taken for repair is", time.time() - solvetime
		self.topology.enableAllEdges()
		# Extract Edge weights for Gurobi	
		print affectedSwitches	
		self.getRepairEdgeWeightModel(edgeWeights, affectedSwitches, self.staticRouteMode)	
		self.pdb.validateControlPlane(self.topology, self.staticRoutes)


	def affectedSwitches(self, oldDags, newDags) :
		""" Find all switches that could be potentially affected 
		to enforce the config repair"""
		affectedSwitches = []
		for dst in oldDags :
			oldDag = oldDags[dst]
			newDag = newDags[dst]

			if oldDag != newDag : 
				# Change for paths to dst 
				for sw in newDag : 
					if sw not in oldDag and sw not in affectedSwitches:
						# New switch. 
						affectedSwitches.append(sw)

					if sw in oldDag and newDag[sw] not in oldDag and sw not in affectedSwitches:
						# Switch where the new path diverges 
						affectedSwitches.append(sw)

		return affectedSwitches

	def initializeRepairVariables(self, edgeWeights, affectedSwitches) : 
		swCount = self.topology.getSwitchCount()
		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.grbedgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 
		
		for sw1 in range(1,swCount+1):
			if sw1 in affectedSwitches: 
				for sw2 in self.topology.getSwitchNeighbours(sw1) :
					self.grbedgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=0.00, ub=10000, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + "_")
					self.edgeWeights[sw1][sw2] = edgeWeights[sw1][sw2] + self.grbedgeWeights[sw1][sw2]
			else :
				for sw2 in self.topology.getSwitchNeighbours(sw1) :
					self.edgeWeights[sw1][sw2] = edgeWeights[sw1][sw2]

		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=0.00, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + "_")

		self.ilpSolver.update()

	def removeInvalidStaticRoutes(self, newDags) :
		""" Remove the static routes which are on paths no longer valid """

		dsts = self.pdb.getDestinationSubnets()
		for dst in dsts : 
			dag = newDags[dst]
			staticRoutes = self.staticRoutes[dst]
			invalidSR = []
			for sr in staticRoutes :
				if sr[0] in dag and sr[1] == dag[sr[0]] : 
					# Static route still valid 
					continue
				else : 
					invalidSR.append(sr)

			# Remove invalid static routes
			for sr in invalidSR : 
				self.staticRoutes[dst].remove(sr)


	def findRepairInconsistency(self, edgeWeights, affectedSwitches) :
		""" Find inconsistent set of equations """
		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)
		self.initializeRepairVariables(edgeWeights, affectedSwitches)
		dsts = self.pdb.getDestinationSubnets()

		self.addDjikstraShortestPathConstraints()
		# Adding constraints with routeFilter variables at source
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw in dag : 
				if sw in affectedSwitches :
					self.addDestinationDAGConstraints(dst, dag)
					break

		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime

		status = self.ilpSolver.status
		if status == gb.GRB.INFEASIBLE :
			solvetime = time.time()
			self.ilpSolver.computeIIS()
			self.z3solveTime += time.time() - solvetime
			self.minimizeRepairStaticRoutes(affectedSwitches)
			return True
		else :
			return False

	def minimizeRepairStaticRoutes(self, affectedSwitches) :
		""" Pick static routes greedily from affectedSwitches """
		staticRoutes = []
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "SR" :
					# Static Route constraint
					#if fields[1] not in affectedSwitches : continue # Dont consider static routes
					foundFlag = False
					for ind in range(len(staticRoutes)) :
						if staticRoutes[ind][0] == [int(fields[1]), int(fields[2]), int(fields[4])] : 
							staticRoutes[ind] = [staticRoutes[ind][0], staticRoutes[ind][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						staticRoutes.append([[int(fields[1]), int(fields[2]), int(fields[4])], 1])

		sr = None
		count = 0
		for ind in range(len(staticRoutes)) : 
			if staticRoutes[ind][1] > count : 
				sr = staticRoutes[ind][0]
				count = staticRoutes[ind][1]

		# Pick the best static Route
		self.addStaticRoute(sr[0], sr[1], sr[2])

	def getRepairEdgeWeightModel(self, oldEdgeWeights, affectedSwitches, staticRouteMode=True) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()
		# self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

		self.edgeWeightValues = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) : 
				if n not in self.overlay[sw] :
					self.topology.addWeight(sw, n, float(100000))
					self.edgeWeightValues[sw][n] = float(100000)
					#print sw, n, 1000
		
		for sw1 in range(1,swCount+1):
			if sw1 in affectedSwitches: 
				for sw2 in self.topology.getSwitchNeighbours(sw1) :
					if sw2 not in self.overlay[sw1]: continue
					self.topology.addWeight(sw1, sw2, self.grbedgeWeights[sw1][sw2].x + oldEdgeWeights[sw1][sw2])
			else :
				for sw2 in self.topology.getSwitchNeighbours(sw1) :
					self.topology.addWeight(sw1, sw2, oldEdgeWeights[sw1][sw2])
					#print sw, n,  float(ew)

		if not staticRouteMode :
			# Route filters not used. 
			return 

		totalStaticRoutes = 0
		setStaticRoutes = 0
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			totalStaticRoutes += len(dag) - 1 
		
		for dst in dsts : 
			setStaticRoutes += len(self.staticRoutes[dst])

		self.SRCount = setStaticRoutes
		print "Ratio of Static Routes : ", setStaticRoutes, totalStaticRoutes 
# nuZ3
# maxSAT
# US Backbone, RocketFuelS