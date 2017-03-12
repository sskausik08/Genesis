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
	def __init__(self, topology, pdb, minimalFilterSolve=False) :
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
		self.t_res = 0

		# Constants
		self.MAX_GUROBI_ITERATIONS = 600
		self.minimalFilterSolveFlag = minimalFilterSolve

		self.inconsistentSRs = 0

		# Gurobi Constraints
		self.distanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.backupPathConstraints = defaultdict(lambda:defaultdict(lambda:None))

	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 
		self.routefiltersVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.maxFlowVars = defaultdict(lambda:defaultdict(lambda:None))

		dsts = self.pdb.getDestinationSubnets()

		for sw1 in range(1,swCount+1):
			for sw2 in self.topology.getSwitchNeighbours(sw1) :
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=1.00, ub=10000, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + "_")

		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=0.00, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + "_")
				# for dst in dsts : 
				# 	self.distVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00,vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2)+"-"+str(dst) + " ")

		self.ilpSolver.update()

	def initializeStaticRoutes(self) :
		self.staticRoutes = dict()
		for dst in self.pdb.getDestinationSubnets() :
			self.staticRoutes[dst] = []

		self.staticRoutes[0] = [] # Default destination val = 0 (Not a s)

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

	def enforceDAGs(self, dags, endpoints, backups=None, bgpExtensions=None):
		""" Enforce the input destination dags """
		start_t = time.time()
		self.overlay = dict()
		self.destinationDAGs = copy.deepcopy(dags)
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

		# Adding constraints without routeFilters
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag, False)

		for dst in backups : 
			backupPaths = backups[dst]
			dag = self.destinationDAGs[dst]
			for backupPath in backupPaths : 
				self.addBackupPathConstraints(dst, dag, backupPath, False) 

		#print "Solving ILP without static routes"
		solvetime = time.time()
		#modelsat = self.z3Solver.check()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime
	
		self.routeFilterMode = False
		status = self.ilpSolver.status

		if status == gb.GRB.INFEASIBLE :
			if self.minimalFilterSolveFlag :
				self.routeFilterMode = True 
				self.minimalFilterSolve()
			else : 
				#print "solving ILP with static routes"
				self.routeFilterMode = True

				#self.findValidCycles()
				self.ilpSolver = gb.Model("C3")
				self.ilpSolver.setParam('OutputFlag', 0)
				self.initializeSMTVariables()

				self.addDjikstraShortestPathConstraints()

				# Prompted by Gurobi? 
				# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
				# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 

				# Adding constraints with routeFilter variables at source
				for dst in dsts : 
					dag = self.destinationDAGs[dst]
					self.addDestinationDAGConstraints(dst, dag)

				for dst in backups : 
					backupPaths = backups[dst]
					dag = self.destinationDAGs[dst]
					for backupPath in backupPaths : 
						self.addBackupPathConstraints(dst, dag, backupPath, True) 

				# if self.t_res > 0 :
				# 	t_res = self.t_res
				# 	for endpt in self.endpoints : 
				# 		self.addResilienceConstraints(endpt[0], endpt[1], t_res)  # Add t-resilience

				solvetime = time.time()
				self.ilpSolver.optimize()
				self.z3solveTime += time.time() - solvetime

				status = self.ilpSolver.status

				while status == gb.GRB.INFEASIBLE :
					# Perform inconsistency analysis using Gurobi
					attempts = 1
					self.ilpSolver.computeIIS()
					self.minimizeStaticRoutes()
					
					solvetime = time.time()
					self.ilpSolver.optimize()
					self.z3solveTime += time.time() - solvetime

					status = self.ilpSolver.status
			
		# self.f.write(str(len(endpoints)) + "," + str(time.time() - start_t)+"\n")
		# Enable Topology Edges
		self.topology.enableAllEdges()
		# Extract Edge weights for Gurobi		
		self.getEdgeWeightModel(self.routeFilterMode)	

		# self.f.close()	
		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.staticRoutes, backups)

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

		
		self.zepFile = open("ospf-timing", 'a')
		self.zepFile.write("Topology Switches\t" +  str(swCount))
		self.zepFile.write("\n")
		print "Time" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(time.time() - start_t)
		self.zepFile.write("Time" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(time.time() - start_t))
		self.zepFile.write("\n")
		self.zepFile.write("Static Routes" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(srCount) + "\t")
		self.zepFile.write("\n")


	def synthesizeRepair(self) :
		# Consider the repair problem now. #Experimental code
		oldDags = copy.deepcopy(self.destinationDAGs)

		changeCount = 4
		random.shuffle(dsts)
		for changedDst in dsts : 
			newDag = self.changeDag(self.destinationDAGs[changedDst])
			if newDag != self.destinationDAGs[changedDst] : 
				self.destinationDAGs[changedDst] = newDag 
				self.pdb.addDestinationDAG(changedDst, newDag)
				changeCount = changeCount - 1

			if changeCount == 0 : 
				break

		if changeCount > 0 : 
			print "Wait, what?"
			exit(0)
		
		self.repair(oldDags, self.destinationDAGs, self.edgeWeightValues)

		return self.staticRouteNames


	def changeDag(self, dag) :
		newDag = copy.deepcopy(dag)

		for sw in newDag : 
			if newDag[sw] == None :
				dstSw = sw
		
		newpath = []
		for sw in newDag :
			if sw != dstSw :
				paths = self.topology.getAllPaths(sw, dstSw)
				if len(paths) <= 1 :
					continue
				for path in paths : 
					# Check if path creates a loop. 
					loopedPath = False
					for i in range(1, len(path) - 1) :  
						loopedPath = False
						if path[i] in newDag : 
							nextsw = path[i] 
							while nextsw != None : 
								if nextsw == sw : 
									# This path loops back to sw. Dont use
									loopedPath = True
									break
								nextsw = newDag[nextsw]

						if loopedPath : 
							break
					if loopedPath : 
						continue

					newpath = [sw]
					# Choose this path
					for i in range(1, len(path)) :
						if path[i] not in newDag : 
							newpath.append(path[i])
						else :
							newpath.append(path[i])
							break
				if len(newpath) > 0 : 
					break
			if len(newpath) > 0 : 
				break			

		for i in range(0, len(newpath) - 1) :
			newDag[newpath[i]] = newpath[i + 1]

		return newDag
	"""
	An IIS is a subset of the constraints and variable bounds of the original model. 
	If all constraints in the model except those in the IIS are removed, the model is still infeasible. 
	However, further removing any one member of the IIS produces a feasible result.
	"""	
	def minimizeStaticRoutes(self) :
		""" Pick static routes greedily """
		staticRoutes = []
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "SR" :
					# Static Route constraint
					foundFlag = False
					for ind in range(len(staticRoutes)) :
						if staticRoutes[ind][0] == [int(fields[1]), int(fields[2]), int(fields[4])] : 
							staticRoutes[ind] = [staticRoutes[ind][0], staticRoutes[ind][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						staticRoutes.append([[int(fields[1]), int(fields[2]), int(fields[4])], 1])

		if len(staticRoutes) == 0 : 
			print "INFEASIBLE forever"
			exit(0)

		sr = None
		count = 0
		for ind in range(len(staticRoutes)) : 
			if staticRoutes[ind][1] > count : 
				sr = staticRoutes[ind][0]
				count = staticRoutes[ind][1]

		# Pick the best static Route
		self.addStaticRoute(sr[0], sr[1], sr[2])

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

	# These constraints are solved fast, does exponentially increase synthesis time.
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
			if dag[sw] == None :
				dstSw = sw

		if not staticRouteMode :
			for sw in dag : 
				t = dag[sw]
				while t != None :				
					self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, dag[sw]) + self.dist(dag[sw], t))

					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n != dag[sw] : 
							self.ilpSolver.addConstr(self.dist(sw, t) <= self.ew(sw, n) + self.dist(n, t) - 1)
							
					t = dag[t]
		else:
			for sw in dag :	
				if sw == dstSw : continue					
				nextsw = sw
				totalDist = 0 # Store the distance from sw to t along dag.
				while nextsw != dstSw : 
					totalDist += self.ew(nextsw, dag[nextsw])
					nextsw = dag[nextsw]

				self.ilpSolver.addConstr(self.dist(sw, dstSw) <= totalDist)
					
				if not [sw, dag[sw]] in self.staticRoutes[dst] : 
					neighbours = self.topology.getSwitchNeighbours(sw)
					self.distanceConstraints[sw][dag[sw]][dst] = []
					for n in neighbours : 
						if n != dag[sw]: 
							if type(totalDist) == float and type(self.ew(sw, n)) == float and type(self.dist(n, dstSw)) == float :
								continue

							distconstr = self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, dstSw) - 1, "SR-" + str(sw) + "-" 
								+ str(dag[sw]) + "-" + str(dstSw) + "-" + str(dst) + "-" + str(self.constraintIndex))
							self.distanceConstraints[sw][dag[sw]][dst].append(distconstr)
							self.constraintIndex += 1

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

		neighbours = self.topology.getSwitchNeighbours(startSw)
		for n in neighbours : 
			if n != origSw and n != backupSw :
				self.ilpSolver.addConstr(backupDist  
					<= self.ew(startSw, n) + self.dist(n, dstSw) - 1)

		origDist = self.ew(startSw, origSw)
		while origSw != dstSw : 
			# Ensure backup path is shorter than the other paths starting at origSw
			neighbours = self.topology.getSwitchNeighbours(origSw)
			for n in neighbours : 
				if n != dag[origSw] : 
					self.ilpSolver.addConstr(backupDist 
						<= origDist + self.ew(origSw, n) + self.dist(n, dstSw) - 1)

			origDist += self.ew(origSw, dag[origSw])
			origSw = dag[origSw]

		# Create a dag from backupSw to dstSw and add shortest path constraints
		backupDag = dict()
		for i in range(1, len(backupPath) - 1):
			backupDag[backupPath[i]] = backupPath[i + 1]
		backupDag[dstSw] = None

		self.addDestinationDAGConstraints(dst, backupDag, staticRouteMode)
		

	def addBGPExtensionConstraints(self, dst, dag, routeFilterMode=True) :
		# TODO: Change wrt static routes
		for tup in self.bgpExtensions: 
			if tup[3] != dst : continue
			src = tup[0]
			end1 = tup[1]
			end2 = tup[2]
			if not routeFilterMode :
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
		for dconstr in distconstrs : 
			self.ilpSolver.remove(dconstr)

		self.ilpSolver.update()
		#print "SR", sw1, sw2, dst


	def getEdgeWeightModel(self, routeFilterMode=True) : 
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
					#print sw, n,  float(ew)


		if not routeFilterMode :
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

	# Profiling Statistics : 
	def printProfilingStats(self) :
		#print "Time taken to add constraints are ", self.z3addTime
		print "Zeppelin: Time taken to solve constraints are ", self.z3solveTime
		# print "Number of z3 adds to the solver are ", self.z3numberofadds

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
		self.getRepairEdgeWeightModel(edgeWeights, affectedSwitches, self.routeFilterMode)	
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

	def getRepairEdgeWeightModel(self, oldEdgeWeights, affectedSwitches, routeFilterMode=True) : 
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


		if not routeFilterMode :
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