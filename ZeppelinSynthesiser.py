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

from enum import Enum
class SRType(Enum):
	SR = 0
	W = 1
	RLA = 2
	RLAR = 3
	WR = 4

class ZeppelinSynthesiser(object) :
	def __init__(self, topology, pdb, resilience=False, waypointCompliance=False) :
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

		self.resilience = resilience
		self.waypointCompliance = waypointCompliance
		self.SRCount = 0
		self.waypoints = dict()
		self.waypointClasses = []
		self.zeppelinPaths = dict()
		self.zeppelinPathTypes = dict()
		self.firstStaticRoutes = defaultdict(lambda:defaultdict(lambda:None))
		self.rlaBackupPaths = dict()

		# Constants
		self.MAX_GUROBI_ITERATIONS = 600
		self.backupFlag = False
		self.maximalBackupFlag = False # maximalBackup
		self.randomWaypoints = False


		self.inconsistentSRs = 0
		self.sourceSRs = 0
		self.inconsistentBPs = 0

		# Gurobi Constraints
		self.distanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.backupPathConstraints = defaultdict(lambda:defaultdict(lambda:None))
		self.firstStaticRouteConstraints = defaultdict(lambda:defaultdict(lambda:None))

	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 

		dsts = self.pdb.getDestinationSubnets()

		for sw1 in range(1,swCount+1):
			for sw2 in self.topology.getSwitchNeighbours(sw1) :
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=1.00, ub=100, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + "_")

		self.distSum = 0
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=1, ub=10000, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + "_")
				self.distSum += self.distVars[sw1][sw2][0]
				# for dst in dsts : 
				# 	self.distVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00,vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2)+"-"+str(dst) + " ")

		self.waypointDistVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None))) 
		self.ilpSolver.update()

	def initializeStaticRoutes(self) :
		self.staticRoutes = dict()
		for dst in self.pdb.getDestinationSubnets() :
			self.staticRoutes[dst] = []

		self.staticRoutes[0] = [] # Default destination val = 0 (Not a s)

		# Gurobi Constraints
		self.distanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.waypointResilienceConstraints =  defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.waypointDistanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.routingLoopAvoidanceConstraints = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
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
	
	def dist(self, sw1, sw2, dst=0) : 
		# Default value of dst = 0
		if sw1 == sw2 : 
			return 0.0
		return self.distVars[sw1][sw2][dst]

	def bp(self, sw, dst) : 
		return self.backupPathVars[sw][dst]

	def enforceDAGs(self, dags, endpoints, waypoints=None, backups=None, bgpExtensions=None):
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
		
		self.waypoints = copy.deepcopy(waypoints)
		
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()

		# self.f = open('timing', 'a')
		# self.f.write(str(dags))
		# self.f.write("\n\n\n")

		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)
	
		self.constructOverlay()	
		#self.overlayConnectivity()	
		self.disableUnusedEdges()
		self.initializeSMTVariables()
		self.initializeStaticRoutes()

		#print "solving ILP with static routes"
		self.staticRouteMode = True

		#self.findValidCycles(
		self.addDjikstraShortestPathConstraints()

		if not self.waypointCompliance: 
			# Prompted by Gurobi? 
			# # self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
			# # self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 
			# if self.backupFlag : 
			# 	for dst in self.backupPaths : 
			# 		backupPaths = self.backupPaths[dst]
			# 		dag = self.destinationDAGs[dst]
			# 		for backupPath in backupPaths : 
			# 			self.addBackupPathConstraints(dst, dag, backupPath, True) 
			self.enforceStrictCompliance()
		else : 
			self.enforceWaypointCompliance(self.resilience)

		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime

		status = self.ilpSolver.status
		attempts = 0
		while status == gb.GRB.INFEASIBLE or status == gb.GRB.INF_OR_UNBD  :
			# Perform inconsistency analysis using Gurobi
			attempts =+ 1
			self.ilpSolver.computeIIS()
			self.repairInconsistency()
			
			solvetime = time.time()
			self.ilpSolver.optimize()
			self.z3solveTime += time.time() - solvetime

			status = self.ilpSolver.status

			if attempts > 1000 : 
				print "Could not solve in 1000 iterations"
				exit(0)
			
		# Extract Edge weights from Gurobi
		self.staticRouteMode = True		
		self.getEdgeWeightModel(self.staticRouteMode)	
			
		end_t = time.time() - start_t

		# Add static routes to ensure there arent any violations
		#self.removeViolations()
		# self.f.close()	
		#self.pdb.printPaths(self.topology)
		#self.pdb.validateControlPlane(self.topology, self.staticRoutes, self.backupPaths)
		#self.pdb.validateControlPlaneResilience(self.topology, self.staticRoutes)
		
		if not self.waypointCompliance : 
			self.pdb.validateControlPlane(self.topology, self.staticRoutes)
		else : 
			self.pdb.validateControlPlaneWaypointCompliance(self.topology, self.staticRoutes, self.waypoints, self.zeppelinPaths)
		
		score = self.pdb.validateControlPlaneResilience(self.topology, self.staticRoutes, self.waypoints, self.zeppelinPaths)
		
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

		
		self.zepFile = open("zeppelin-timing", 'a')
		# self.zepFile.write("Topology Switches\t" +  str(swCount))
		# self.zepFile.write("\n")
		self.zepFile.write(str(len(self.waypointClasses)) + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(end_t) + "\t" + str(self.SRCount) +"\t" + str(self.totalSRCount) + "\t" + str(self.waypointCompliance) + "\t" + str(self.resilience) + "\t" + str(score[0]) + "\t" + str(score[1]))
		self.zepFile.write("\n")
		self.zepFile.close()
		# self.zepFile.write("Static Routes" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(srCount) + "\t")
		# self.zepFile.write("\n")

		#return self.staticRouteNames

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
					self.ilpSolver.addConstr(self.dist(s, t) <= self.ew(s, sw) + self.dist(sw, t), 
						"D-" + str(s) + "-" + str(sw) + "-" + str(t))	
					self.constraintIndex += 1

	def enforceStrictCompliance(self) : 
		swCount = self.topology.getSwitchCount()
		
		for pc in range(self.pdb.getPacketClassRange()) : 
			dst = self.pdb.getDestinationSubnet(pc)
			path = self.pdb.getPath(pc)
			dag = self.destinationDAGs[dst]
			dstSw = path[len(path)-1]

			if dst not in self.zeppelinPaths : 
				self.zeppelinPaths[dst] = []
				self.zeppelinPaths[dst].append(path)
			else : 
				self.zeppelinPaths[dst].append(path)

		dsts = self.pdb.getDestinationSubnets()
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag)

	def addDestinationDAGConstraints(self, dst, dag, staticRouteMode=True) :
		""" Adds constraints such that dag weights are what we want them to be with static routing disabled/enabled """	
		for sw in dag :
			if dag[sw] == None : continue 
			if self.distanceConstraints[sw][dag[sw]][dst] == None : 
				self.distanceConstraints[sw][dag[sw]][dst] = []
			for path in self.zeppelinPaths[dst] :
				if sw in path and dag[sw] in path : 
					pathID = self.zeppelinPaths[dst].index(path)
					break

			pathDist = self.ew(sw, dag[sw])
			t = dag[sw] 
			while t != None :				
				# distconstr = self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, dag[sw]) + self.dist(dag[sw], t), 
				# 	"SR-" + str(sw) + "-" + str(dag[sw]) + "-" + str(t) + "-" + str(dst) + "-" + str(self.constraintIndex))
				
				# self.distanceConstraints[sw][dag[sw]][dst].append(distconstr)
				# self.constraintIndex += 1
			
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n != dag[sw] : 
						distconstr = self.ilpSolver.addConstr(pathDist <= self.ew(sw, n) + self.dist(n, t) - 1, 
							"SR-" + str(sw) + "-" + str(dag[sw]) + "-" + str(dst) + "-" + str(pathID))
						
						self.distanceConstraints[sw][dag[sw]][dst].append(distconstr)

				if dag[t] != None : 
					pathDist += self.ew(t, dag[t])
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

	def getEdgeWeightModel(self, staticRouteMode=True) : 
		self.zepOutputFile = open("zeppelin-output", 'w')
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
					self.topology.addWeight(sw, n, int(10*float(ew)))
					self.edgeWeightValues[sw][n] = int(10*float(ew))
					self.zepOutputFile.write("EW " + str(sw) + " " + str(n) + " " + str(int(10*float(ew))) + "\n")

		for sw1 in range(1, swCount + 1) :
			for sw2 in range(1, swCount + 1) :
				if sw1 == sw2 : continue

				dist = self.dist(sw1, sw2).x
				wdist = -1
				self.zepOutputFile.write("D " + str(sw1) + " " + str(sw2) + " " + str(float(dist)) + " " + str(float(wdist)) + "\n")
				#print "D ", sw1, sw2, dist, wdist

		if not staticRouteMode :
			# Route filters not used. 
			return 

		self.totalSRCount = 0
	
		self.edges = []	
		for dst in dsts : 
			self.SRCount += len(self.staticRoutes[dst])
			for sr in self.staticRoutes[dst] :
				if sr not in self.edges : 
					self.edges.append(sr)

		for dst in dsts : 
			edges = []
			for path in self.zeppelinPaths[dst] : 
				for index in range(len(path) - 1):
					if [path[index], path[index + 1]] not in edges :  
						edges.append([path[index], path[index + 1]])
			self.totalSRCount += len(edges)
				
		self.SRCount
		print "Ratio of Static Routes : ", self.SRCount, self.totalSRCount 
		#print "Edges used", len(self.edges), totEdges


	# Profiling Statistics : 
	def printProfilingStats(self) :
		#print "Time taken to add constraints are ", self.z3addTime
		print "Zeppelin: Time taken to solve constraints are ", self.z3solveTime
		# print "Number of z3 adds to the solver are ", self.z3numberofadds

	"""
	An IIS is a subset of the constraints and variable bounds of the original model. 
	If all constraints in the model except those in the IIS are removed, the model is still infeasible. 
	However, further removing any one member of the IIS produces a feasible result.
	"""	
	def repairInconsistency(self) :
		""" Pick static routes/ remove backup paths greedily """
		# for constr in self.ilpSolver.getConstrs() :
		# 	if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
		# 		print constr.getAttr(gb.GRB.Attr.ConstrName) 

		staticRoutes = []
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "SR" :
					# Static Route constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [SRType.SR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[3])] : 
							# Compute score for static route
							staticRoutes.append([[SRType.SR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])], 1])
	
				elif fields[0] == "W" :
					# waypoint path distance constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [SRType.W, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[3])] : 
							# Compute score for static route
							staticRoutes.append([[SRType.W, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])], 1])

				elif fields[0] == "WR" :
					# resilient waypoint path distance constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [SRType.WR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[3])] : 
							# Compute score for static route
							staticRoutes.append([[SRType.WR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])], 1])

				elif fields[0] == "RLA" : 
					# Routing loop avoidance constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [SRType.RLA, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[3])] : 
							# Compute score for static route
							staticRoutes.append([[SRType.RLA, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])], 1])

				elif fields[0] == "RLAR" : 
					# resilience Routing loop avoidance constraint
					foundFlag = False
					for index in range(len(staticRoutes)) :
						if staticRoutes[index][0] == [SRType.RLAR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])] : 
							staticRoutes[index] = [staticRoutes[index][0], staticRoutes[index][1] + 1]
							foundFlag = True
							break
					if not foundFlag :
						if [int(fields[1]), int(fields[2])] not in self.staticRoutes[int(fields[3])] : 
							# Compute score for static route
							staticRoutes.append([[SRType.RLAR, int(fields[1]), int(fields[2]), int(fields[3]), int(fields[4])], 1])

		if len(staticRoutes) > 0 : 
			random.shuffle(staticRoutes)
			print "SRs", staticRoutes

			# Check if there is a static route leadint to dstSw
			chosenSR = None
			for sr in staticRoutes : 
				dag = self.destinationDAGs[sr[0][3]]
				for sw in dag :
					if dag[sw] == None : 
						dstSw = sw
				if dstSw == sr[0][2] :
					# Pick this static route! 
					chosenSR = sr[0]
					break

			if chosenSR == None : 
				# Check if a static route starts at a switch with no backup paths
				for sr in staticRoutes : 
					sw1 = sr[0][1]
					dag = self.destinationDAGs[sr[0][3]]
					for sw in dag :
						if dag[sw] == None : 
							dstSw = sw
					mincut = self.topology.findMinCut(sw1, dstSw)
					if mincut == 1 : 
						# No backup path at sw1. Pick this static route.
						chosenSR = sr[0]
						#print "Picked the static route at switch with no backup paths!"
						break

			if chosenSR == None : 
				# Check if a static route ends at a switch with no back up paths'
				nonResilientStaticRoutes = []
				for sr in staticRoutes : 
					sw2 = sr[0][2]
					dag = self.destinationDAGs[sr[0][3]]
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
				sourceStaticRoutes = []
				for sr in staticRoutes : 
					sw1 = sr[0][1]
					dst = sr[0][3]
					for path in self.zeppelinPaths[dst] : 
						if path[0] == sw1 : 
							# Source static route. 
							if sr not in sourceStaticRoutes : 
								sourceStaticRoutes.append(sr)
							break
				
				if len(sourceStaticRoutes) == len(staticRoutes) :
					print "No option than to add static routes at source"
					#self.findBestSourceStaticRoute(staticRoutes)
					
				else :
					# Choose from resilient filters. 
					for sr in sourceStaticRoutes :
						staticRoutes.remove(sr)

				count = 0
				for ind in range(len(staticRoutes)) : 
					if staticRoutes[ind][1] > count : 
						chosenSR = staticRoutes[ind][0]
						count = staticRoutes[ind][1]
			
			success = False
			# Pick the best static Route
			success = self.addStaticRoute(srtype=chosenSR[0], sw1=chosenSR[1], sw2=chosenSR[2], dst=chosenSR[3], pathID=chosenSR[4])

			if not success : 
				print "===========?IIS?============="
				for constr in self.ilpSolver.getConstrs() :
					if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
						print constr 
				exit(0)

		else : 
			print "===========?IIS?============="
			for constr in self.ilpSolver.getConstrs() :
				if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
					name = constr.getAttr(gb.GRB.Attr.ConstrName) 
					fields = name.split("-")
					if fields[0] == "noSR" :
						dst = int(fields[3])
						pathID = int(fields[4])

						fsrConstraint = self.firstStaticRouteConstraints[dst][pathID]	
						print "Removing waypoint distance constraint", fields
						self.ilpSolver.remove(fsrConstraint)
						self.firstStaticRouteConstraints[dst][pathID] = None
						self.ilpSolver.update()
						return
				
				

	def addStaticRoute(self, srtype, sw1, sw2, dst, pc=None, pathID=None) :
		""" Add rf at sw1 -> sw2 for dst """
		# Type = SR, W, RLA
		if [sw1, sw2] in self.staticRoutes[dst] :
			print "Static route already exists"
			return False

		if [sw1, sw2] not in self.staticRoutes[dst] :
			self.staticRoutes[dst].append([sw1, sw2]) 
			self.inconsistentSRs += 1

		if srtype == SRType.SR : 
			# Delete distance constraints from model
			# Normal Path is input
			print "SR", sw1, sw2, dst
		
		distconstrs = self.distanceConstraints[sw1][sw2][dst]
		if distconstrs != None : 
			for dconstr in distconstrs : 
				self.ilpSolver.remove(dconstr)

			#dag = self.destinationDAGs[dst]
			#self.addRoutingLoopAvoidanceConstraints(dst, dag, [sw1, sw2], False)

		if srtype == SRType.W : 
			print "W", sw1, sw2, dst
		
		wconstrs = self.waypointResilienceConstraints[sw1][sw2][dst]
		if wconstrs != None : 
			#print "SR", sw1, sw2, dst
			for wconstr in wconstrs : 
				self.ilpSolver.remove(wconstr)

		# Can remove waypoint distance constraints. 
		# neighbours = self.topology.getSwitchNeighbours(sw1)
		# for n in neighbours : 
		# 	if n == sw2 : continue
		# 	wdconstrs = self.waypointDistanceConstraints[sw1][n][pc]
		# 	if wdconstrs != None :
		# 		for wdconstr in wdconstrs : 
		# 			self.ilpSolver.remove(wdconstr)

		if srtype == SRType.RLA : 
			print "RLA", sw1, sw2, dst

		if srtype == SRType.WR : 
			print "WR", sw1, sw2, dst
	
		if srtype == SRType.RLAR : 
			print "RLAR", sw1, sw2, dst

		if self.waypointCompliance : 
			if srtype == SRType.RLAR or srtype == SRType.WR :
				#currpath = self.rlaBackupPaths[dst][pathID]
				currpath = self.zeppelinPaths[dst][pathID]
				self.addRoutingLoopAvoidanceConstraints(srtype, dst, currpath, [sw1, sw2], False)
			else : 
				currpath = self.zeppelinPaths[dst][pathID]
				self.addRoutingLoopAvoidanceConstraints(srtype, dst, currpath, [sw1, sw2], True)

			if srtype == SRType.W or srtype == SRType.WR : 
				self.addWaypointResilienceConstraints(sw1, sw2, dst, currpath)

		rlaconstrs = self.routingLoopAvoidanceConstraints[sw1][sw2][dst]
		if rlaconstrs != None : 
			#print "SR", sw1, sw2, dst
			for rlaconstr in rlaconstrs : 
				self.ilpSolver.remove(rlaconstr)

		self.ilpSolver.update()
		
		return True	
	
	def findBestSourceStaticRoute(staticRoutes) : 
		""" Find best static route in the source static routes """ 
		for sr in staticRoutes : 
			sw1 = sr[0][1]
			sw2 = sr[0][2]
			dst = sr[0][3]


	# Routing loop avoidance
	def addRoutingLoopAvoidanceConstraints(self, srtype, dst, dstpath, sr, resilience=False) :
		# If sr is added for dst, ensure that a link failure on dag does not cause a loop
		dstSw = dstpath[len(dstpath) - 1]
		print dstpath, sr

		if sr[1] == dstSw :
			# No need for routing loop avoidance
			return

		if srtype == SRType.RLAR : 
			dstpathID = self.rlaBackupPaths[dst].index(dstpath)
		else : 
			for path in self.zeppelinPaths[dst] : 
				if sr[0] in path and sr[1] == path[path.index(sr[0]) + 1] : 
					dstpath = path
					dstpathID = self.zeppelinPaths[dst].index(dstpath)
					break
			# if dstpath not in self.zeppelinPaths[dst] : 
			# 	self.zeppelinPaths.append(dstpath)
			

		start = dstpath.index(sr[1])
		dstpathDist = 0
		for index in range(start, len(dstpath) - 1) : 
			dstpathDist += self.ew(dstpath[index], dstpath[index + 1])

		if srtype == SRType.WR : 
			srname = ""
			# Check to see if SR is just WR or W as well. 
			for wpath in self.zeppelinPaths[dst] : 
				if self.zeppelinPathTypes[dst] == "W" and sr[1] in wpath and dstpath[start + 1] == wpath[wpath.index(sr[1]) + 1] : 
					# THis is a static route on a primary path. 
					srname = "W-" + str(sr[1]) + "-" + str(dstpath[start + 1]) + "-" + str(dst) + "-" + str(0) + "-" + str(dstpathID)
					print "W in WR no res", srname
					break

			if srname == "" : 
				# RLAR constraint.
				srname = "WR-" + str(sr[1]) + "-" + str(dstpath[start + 1]) + "-" + str(dst) + "-" + str(dstpathID)
		
		else : 
			srname = "W" + "-" + str(sr[1]) + "-" + str(dstpath[start + 1]) + "-" + str(dst) + "-" + str(dstpathID)
		
		intersectingPaths = []
		otherPaths = []
		for wpath in self.zeppelinPaths[dst] : 
			if sr[1] in wpath :
				intersectingPaths.append(wpath)
			else : 
				otherPaths.append(wpath)

		if dst in self.rlaBackupPaths : 
			for rlapath in self.rlaBackupPaths[dst] : 
				if sr[1] in rlapath :
					intersectingPaths.append(rlapath)

		for path in intersectingPaths : 
			# All upstream paths must not be part of a loop.
			startIndex = path.index(sr[1])
			if [sr[1], dstpath[start + 1]] not in self.staticRoutes[dst] : 
				if self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst] == None:
					self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst] = []

				for index in range(startIndex) : 
					rlaconstr = self.ilpSolver.addConstr(dstpathDist <= self.dist(sr[1], path[index]) + self.dist(path[index], dstSw) - 1, 
						srname)

					self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst].append(rlaconstr)

		for path in otherPaths : 
			if [sr[1], dstpath[start + 1]] not in self.staticRoutes[dst] : 
				if self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst] == None:
					self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst] = []

				for index in range(len(path) - 1) : 
					if path[index] in dstpath : break
					rlaconstr = self.ilpSolver.addConstr(dstpathDist <= self.dist(sr[1], path[index]) + self.dist(path[index], dstSw) - 1, 
						srname)

					self.waypointResilienceConstraints[sr[1]][dstpath[start + 1]][dst].append(rlaconstr)

		return 
		

	# 	# Find a dstpath from sr[1] tp dstSw which is edge-disjoint to dstpath
	# 	dagEdges = []
	# 	for index in range(len(dstpath) - 1): 
	# 		dagEdges.append([dstpath[index], dstpath[index + 1]])
	# 		neighbours = self.topology.getSwitchNeighbours(dstpath[index])
	# 		for n in neighbours : 
	# 			dagEdges.append([n, dstpath[index]])

	# 	# append upstream switch edges of other paths which use sr[1]
	# 	for wpath in self.zeppelinPaths[dst] :
	# 		if wpath == dstpath : continue 
	# 		if sr[1] in wpath : 
	# 			for index in range(wpath.index(sr[1])) : 
	# 				neighbours = self.topology.getSwitchNeighbours(wpath[index])
	# 				for n in neighbours : 
	# 					dagEdges.append([n, wpath[index]])
				

	# 	neighbours = self.topology.getSwitchNeighbours(sr[1])
	# 	for nsw in neighbours : 
	# 		if nsw == sr[0] or nsw == dstpath[start + 1] : # DOnt add these constraints on switches on the path
	# 			continue
	# 		backupPath = []
	# 		while len(backupPath) == 0 : 
	# 			backupPath = self.topology.getBFSPath(nsw, dstSw, dagEdges)
	# 			if backupPath == [] : 
	# 				# No dstpath  
	# 				print "No alternate dstpath", dst, sr, nsw, dstSw, self.topology.findMinCut(sr[1], dstSw)
	# 				break
			
	# 		if backupPath == [] : 
	# 			continue

	# 		newBackupPath = []
	# 		for index in range(len(backupPath) - 1) :
	# 			bpsw = backupPath[index]
	# 			shortest = []
	# 			shortestLen = 1000000 
	# 			for path in self.zeppelinPaths[dst] : 
	# 				if bpsw in path : 
	# 					# Found a path to dst 
	# 					bplen = len(path) - path.index(bpsw) - 1
	# 					if bplen < shortestLen : 
	# 						shortest = path
	# 						shortestLen = bplen

	# 			if len(shortest) > 0 : 
	# 				# Found a backup path with least distance to dst. Use that.
	# 				print backupPath, bpsw, shortest
	# 				newBackupPath = backupPath[:backupPath.index(bpsw)]
	# 				newBackupPath.extend(shortest[shortest.index(bpsw):])
	# 				break

	# 		if newBackupPath != [] : 
	# 			backupPath = newBackupPath

	# 		# Store backup path.
	# 		if dst not in self.rlaBackupPaths: 
	# 			self.rlaBackupPaths[dst] = []

	# 		completePath = dstpath[:start + 1]
	# 		completePath.extend(backupPath)
	# 		self.rlaBackupPaths[dst].append(completePath) # Add backup path to record
	# 		rlapathID = self.rlaBackupPaths[dst].index(completePath)
	# 		print "Routing loop resilience", dst, dstpath, sr, backupPath, completePath
			
	# 		bpDist = 0
	# 		for index in range(len(backupPath) - 1):
	# 			bpDist += self.ew(backupPath[index], backupPath[index + 1])
			
	# 		for wpath in self.zeppelinPaths[dst] : 
	# 			if sr[1] not in wpath : continue
	# 			# All upstream paths must not be part of a loop.
	# 			startIndex = wpath.index(sr[1])

	# 			# General routing loop avoidance constraints, cant install static routes for this
	# 			for index in range(startIndex) : 
	# 				# direct edge to dst. Cant put a static route here
	# 				self.ilpSolver.addConstr(self.ew(sr[1], nsw) + bpDist <=  self.dist(sr[1], wpath[index]) + self.dist(wpath[index], dstSw) - 1, 
	# 					"noSR-" + str(sr[1]) + "-" + str(backupPath[0]) + "-" + str(dst) + "-" + str(rlapathID))

	# 			if len(backupPath) > 1 and [backupPath[0], backupPath[1]] not in self.staticRoutes[dst] : 
	# 				# Ensure backup path is shorter than the distance from upstream paths

	# 				srname = ""
	# 				# Check to see if SR is just RLAR or W as well. 
	# 				for wpath2 in self.zeppelinPaths[dst] : 
	# 					if backupPath[0] in wpath2 and backupPath[1] in wpath2 : 
	# 						# THis is a static route on a primary path. 
	# 						srname = "W-" + str(backupPath[0]) + "-" + str(backupPath[1]) + "-" + str(dst) + "-" + str(0) + "-" + str(self.zeppelinPaths[dst].index(wpath2))
	# 						print "W in RLAR", srname
	# 						break

	# 				if srname == "" : 
	# 					# RLAR constraint.
	# 					srname = "RLAR-" + str(backupPath[0]) + "-" + str(backupPath[1]) + "-" + str(dst) + "-" + str(rlapathID)

	# 				if self.routingLoopAvoidanceConstraints[backupPath[0]][backupPath[1]][dst] == None:
	# 					self.routingLoopAvoidanceConstraints[backupPath[0]][backupPath[1]][dst] = []
					
	# 				for index in range(startIndex) : 
	# 					rlaconstr = self.ilpSolver.addConstr(bpDist <=  self.dist(nsw, wpath[index]) + self.dist(wpath[index], dstSw) - 1, 
	# 						srname)
					
	# 					self.routingLoopAvoidanceConstraints[backupPath[0]][backupPath[1]][dst].append(rlaconstr)

	# # Backup Functions

	def initializeWaypointVariables(self) : 
		swCount = self.topology.getSwitchCount()
		
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				for index in range(len(self.waypointClasses)) : 
					self.waypointDistVars[sw1][sw2][index] = self.ilpSolver.addVar(lb=1.00, vtype=gb.GRB.CONTINUOUS, 
						name="W-" + str(sw1)+"-"+str(sw2) + "-" + str(index) + "_")

		self.ilpSolver.update()

	def wdist(self, sw1, sw2, wclass) : 
		if sw1 == sw2 : 
			return 0.0
		if wclass >= len(self.waypointClasses) : 
			print "ERROR, Waypoint Class does not exist", sw1, sw2, wclass, self.waypoints, self.waypointClasses
			exit(0)
		
		return self.waypointDistVars[sw1][sw2][wclass]

	def getWClass(self, dst) : 
		if dst not in self.waypoints : 
			print "ERROR, Waypoint Class does not exist"
			exit(0)
		waypoints = self.waypoints[dst]
		wclass = self.waypointClasses.index(waypoints)
		return wclass

	def addWaypointDjikstraShortestPathConstraints(self) :
		swCount = self.topology.getSwitchCount()

		for wclass in range(len(self.waypointClasses)) :
			waypoints = self.waypointClasses[wclass]
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
						
						wconstr = self.ilpSolver.addConstr(self.wdist(s, t, wclass) <= self.ew(s, sw) + self.wdist(sw, t, wclass), 
							"Wd-" + str(s) + "-" + str(sw) + "-" + str(t) + "-" + str(wclass))	
						
						if self.waypointDistanceConstraints[s][sw][wclass] == None : 
							self.waypointDistanceConstraints[s][sw][wclass] = []
						self.waypointDistanceConstraints[s][sw][wclass].append(wconstr)

					self.ilpSolver.addConstr(self. wdist(s, t, wclass) >= self.dist(s, t), "Dw-" + str(self.constraintIndex) + " ")	
					self.constraintIndex += 1

	def addWaypointComplianceConstraints(self, dst, waypointPath, pathtype="W") : 
		# Add constraints to ensure path goes through atleast one waypoint.	
		dstSw = waypointPath[len(waypointPath) - 1]

		#print dstSw, dags
		if pathtype == "WR" : 
			print "Alternate waypoint path", dst, waypointPath
		
		pathID = self.zeppelinPaths[dst].index(waypointPath)

		for start in range(len(waypointPath) - 1) : 
			if waypointPath[start] in self.waypoints[dst] : 
				break

			if [waypointPath[start], waypointPath[start + 1]] in self.staticRoutes[dst] : 
				# Statically routed at this point
				continue

			pathDist = 0
			for index in range(start, len(waypointPath) - 1) :
				pathDist += self.ew(waypointPath[index], waypointPath[index+1])

			if self.waypointResilienceConstraints[waypointPath[start]][waypointPath[start + 1]][dst] == None : 
				self.waypointResilienceConstraints[waypointPath[start]][waypointPath[start + 1]][dst] = []
			
			neighbours = self.topology.getSwitchNeighbours(waypointPath[start])
			for n in neighbours : 
				if n == waypointPath[start + 1] or n in self.waypoints[dst] : continue
				
				# Path distance must be smaller than non waypoint distance
				wconstr = self.ilpSolver.addConstr(pathDist <= self.ew(waypointPath[start], n) + self.wdist(n, dstSw, self.getWClass(dst)) - 1, 
					pathtype + "-" + str(waypointPath[start]) + "-" + str(waypointPath[start + 1]) + "-" + str(dst) + "-" + str(pathID))

				self.waypointResilienceConstraints[waypointPath[start]][waypointPath[start + 1]][dst].append(wconstr)

	def addWaypointResilienceConstraints(self, sw1, sw2, dst, dstpath) : 
		if not self.resilience : 
			return

		for sw in self.destinationDAGs[dst] :
			if self.destinationDAGs[dst][sw] == None : 
				dstSw = sw
				break

		#start = dstpath.index(sw2)
		for path in self.zeppelinPaths[dst] :
			changeFlag = False
			if sw1 in path and sw2 == path[path.index(sw1) + 1] : 
				# SR in path. See if first static route.
				pathID = self.zeppelinPaths[dst].index(path)
				if self.firstStaticRoutes[dst][pathID] == None : 
					self.firstStaticRoutes[dst][pathID] = [sw1, sw2]
					changeFlag = True
				elif path.index(self.firstStaticRoutes[dst][pathID][0]) > path.index(sw1) : 
					self.firstStaticRoutes[dst][pathID] = [sw1, sw2]
					changeFlag = True
			
			if changeFlag: 
				pathID = self.zeppelinPaths[dst].index(path)
				fsrConstraint = self.firstStaticRouteConstraints[dst][pathID]
				if fsrConstraint != None : 
					self.ilpSolver.remove(fsrConstraint)

				for path2 in self.zeppelinPaths[dst] : 
					if path2[0] == path[0] and path2 != path: 
						bpDist = 0
						for index in range(len(path2) - 1) : 
							bpDist += self.ew(path2[index], path2[index + 1])

						fsrDist = 0
						for index in range(path.index(sw1)) : 
							fsrDist += self.ew(path[index], path[index + 1])

						newfsrConstraint = self.ilpSolver.addConstr(bpDist <= fsrDist + self.dist(sw1, dstSw), 
							"noSR-" + str(sw1) + "-" + str(sw2) + "-" + str(dst) + "-" + str(pathID))
						
						self.firstStaticRouteConstraints[dst][pathID] = newfsrConstraint		

		self.ilpSolver.update()		
		dstpathID = self.zeppelinPaths[dst].index(dstpath)
		if self.zeppelinPathTypes[dst][dstpathID] == "WR" : 
			# Dont need to add another path for this.
			return

		connectedToSrc = True
		#for index in range(len(dstpath) - 1) :
		for index in range(1) :
			if [dstpath[index], dstpath[index + 1]] == [sw1, sw2] and connectedToSrc : 
				# Need to add another resilient dstpath at sw2
				
				waypointPath = self.getWaypointPath(sw2, dstSw, dstpath, dst)	# FInd best intersecting waypoint dstpath
				if len(waypointPath) > 0 : 
					self.zeppelinPaths[dst].append(waypointPath)
					self.zeppelinPathTypes[dst].append("WR")
					self.addWaypointComplianceConstraints(dst, waypointPath, "WR")

			# elif [dstpath[index], dstpath[index + 1]] == [sw1, sw2] and not connectedToSrc : 
			# 	# Find if waypoint traversal happens after sr
			# 	for index in range(len(dstpath) - 1) : 
			# 		if dstpath[index] in self.waypoints[dst] and index <= start : 
			# 			# Dont care about waypoint compliance
			# 			backupPath = self.getWaypointPath(sw2, dstSw, dstpath, dst, False) # Dont need to traverse waypoint in backupPath
			# 			completePath = dstpath[:start]
			# 			completePath.extend(backupPath)
			# 			self.zeppelinPaths[dst].append(completePath)
			# 			self.zeppelinPathTypes[dst].append("WR")

			# 			self.addRoutingLoopAvoidanceConstraints(self, SRType.WR, dst, completePath, [sw1, sw2])

			# 		else :
			# 			waypointPath = self.getWaypointPath(sw2, dstSw, dstpath, dst, True) 
			# 			if len(waypointPath) > 0 : 
			# 				self.zeppelinPaths[dst].append(waypointPath)
			# 				self.zeppelinPathTypes[dst].append("WR")
			# 				self.addWaypointComplianceConstraints(dst, waypointPath, "WR")

			# 	if [path[index], path[index + 1]] not in self.staticRoutes[dst] : 
			# 		connectedToSrc = False

	# def getWaypointPath(self, srcSw, dstSw, path, dst, waypointFlag=True) : 
	# 	dagEdges = []
	# 	for index in range(len(path) - 1) :
	# 		sw = path[index]
	# 		dagEdges.append([sw, path[index + 1]]) 
	# 		if sw == dstSw : continue
	# 		#neighbours = self.topology.getSwitchNeighbours(sw)
	# 		# for n in neighbours : 
	# 		# 	dagEdges.append([n, sw])

	# 	# append upstream switch edges of other paths
	# 	for wpath in self.zeppelinPaths[dst] :
	# 		if srcSw in wpath : 
	# 			for index in range(wpath.index(srcSw)) : 
	# 				neighbours = self.topology.getSwitchNeighbours(wpath[index])
	# 				for n in neighbours : 
	# 					dagEdges.append([n, wpath[index]])

	# 	if waypointFlag : 
	# 		waypointPath = self.topology.getWaypointPaths(srcSw, dstSw, self.waypoints[dst], self.zeppelinPaths[dst], dagEdges)
	# 	else : 
	# 		waypointPath = self.topology.getWaypointPaths(srcSw, dstSw, [], self.zeppelinPaths[dst], dagEdges)

	# 	return waypointPath
	
	def getWaypointPath(self, srcSw, dstSw, path, dst, waypointFlag=True) : 
		dagEdges = []
		for index in range(len(path) - 1) :
			sw = path[index]
			dagEdges.append([sw, path[index + 1]]) 
			if sw == dstSw : continue
			neighbours = self.topology.getSwitchNeighbours(sw)
			for n in neighbours : 
				dagEdges.append([n, sw])

		# append upstream switch edges of other paths
		for wpath in self.zeppelinPaths[dst] :
			if wpath == path : continue 
			if srcSw in wpath : 
				for index in range(wpath.index(srcSw)) : 
					neighbours = self.topology.getSwitchNeighbours(wpath[index])
					for n in neighbours : 
						dagEdges.append([n, wpath[index]])

		if waypointFlag : 
			waypointPaths = self.topology.getWaypointPaths(srcSw, dstSw, self.waypoints[dst], dagEdges)
		else : 
			waypointPaths = self.topology.getWaypointPaths(srcSw, dstSw, [], dagEdges)

		for waypointPath in waypointPaths : 
			#TODO: merge to DAG
			newWaypointPath = []
			for index in range(1, len(waypointPath) - 1) :
				wsw = waypointPath[index]
				shortest = []
				shortestLen = 1000000 
				for path2 in self.zeppelinPaths[dst] : 
					if wsw in path2 : 
						# Found a path2 to dst 
						bplen = len(path2) - path2.index(wsw) - 1
						if bplen < shortestLen : 
							shortest = path2
							shortestLen = bplen

				if len(shortest) > 0 : 
					# Found a backup path with least distance to dst. Use that.
					newWaypointPath = waypointPath[:waypointPath.index(wsw)]
					newWaypointPath.extend(shortest[shortest.index(wsw):])
					break

			if newWaypointPath != [] : 
				waypointPath = newWaypointPath

			# Check waypoint validity
			validPath = False
			for w in self.waypoints[dst] : 
				if w in waypointPath: 
					validPath = True 
					break

			if validPath : 
				return waypointPath

	
		return []


	def enforceWaypointCompliance(self, resilience=False) : 
		swCount = self.topology.getSwitchCount()
		
		for pc in range(self.pdb.getPacketClassRange()) : 
			dst = self.pdb.getDestinationSubnet(pc)
			path = self.pdb.getPath(pc)
			dag = self.destinationDAGs[dst]
			dstSw = path[len(path)-1]

			if dst not in self.zeppelinPaths : 
				self.zeppelinPaths[dst] = []
				self.zeppelinPathTypes[dst] = []
				self.zeppelinPaths[dst].append(path)
				self.zeppelinPathTypes[dst].append("W")
			else : 
				self.zeppelinPaths[dst].append(path)
				self.zeppelinPathTypes[dst].append("W")

			if self.randomWaypoints: 
				waypoints = [path[int((len(path) - 1)/2)]]

				if dst in self.waypoints : 
					for w in waypoints : 
						if w not in self.waypoints[dst] : 
							self.waypoints[dst].append(w)
				else : 
					self.waypoints[dst] = waypoints

		if resilience: 
			for pc in range(self.pdb.getPacketClassRange()) : 
				dst = self.pdb.getDestinationSubnet(pc)
				path = self.pdb.getPath(pc)
				dag = self.destinationDAGs[dst]
				srcSw = path[0]
				dstSw = path[len(path)-1]
				dagEdges = []
				# for index in range(len(path) - 1) :
				# 	sw = path[index]
				# 	dagEdges.append([sw, path[index + 1]]) 
				# 	if sw == dstSw : continue
				# 	neighbours = self.topology.getSwitchNeighbours(sw)
				# 	for n in neighbours : 
				# 		dagEdges.append([n, sw])

				# # append upstream switch edges of other paths
				# for wpath in self.zeppelinPaths[dst] :
				# 	if wpath == path : continue 
				# 	if path[0] in wpath : 
				# 		for index in range(wpath.index(path[0])) : 
				# 			neighbours = self.topology.getSwitchNeighbours(wpath[index])
				# 			for n in neighbours : 
				# 				dagEdges.append([n, wpath[index]])

				# waypointPath = self.topology.getWaypointPath(path[0], path[len(path)-1], self.waypoints[dst], dagEdges)
				# if len(waypointPath) != 0 :
				# 	#TODO: merge to DAG
				# 	newWaypointPath = []
				# 	for index in range(1, len(waypointPath) - 1) :
				# 		wsw = waypointPath[index]
				# 		shortest = []
				# 		shortestLen = 1000000 
				# 		for path in self.zeppelinPaths[dst] : 
				# 			if wsw in path : 
				# 				# Found a path to dst 
				# 				bplen = len(path) - path.index(wsw) - 1
				# 				if bplen < shortestLen : 
				# 					shortest = path
				# 					shortestLen = bplen

				# 		if len(shortest) > 0 : 
				# 			# Found a backup path with least distance to dst. Use that.
				# 			newWaypointPath = waypointPath[:waypointPath.index(wsw)]
				# 			newWaypointPath.extend(shortest[shortest.index(wsw):])
				# 			break

				# 	if newWaypointPath != [] : 
				# 		print "WP", pc, waypointPath, newWaypointPath
				# 		waypointPath = newWaypointPath

				# 	# Check if waypoint path is actually valid
				# 	validPath = False
				# 	for w in self.waypoints[dst] : 
				# 		if w in waypointPath: 
				# 			validPath = True 
				# 			break
				waypointPath = self.getWaypointPath(srcSw, dstSw, path, dst)
				if len(waypointPath) > 0 : 
					self.zeppelinPaths[dst].append(waypointPath)
					self.zeppelinPathTypes[dst].append("W")
				else : 
					print "Waypoint min cut ", self.topology.findMinCut(path[0], path[len(path)-1])

		# Sort waypoint Classes
		for dst in self.waypoints : 
			W = self.waypoints[dst]
			self.waypoints[dst] = sorted(W)

		print self.waypoints 
		for dst in self.waypoints : 
			W = self.waypoints[dst]

			if W not in self.waypointClasses : 
				self.waypointClasses.append(W)

		self.initializeWaypointVariables()
		# Adding waypoint distance constraints for the waypoint classes. 
		self.addWaypointDjikstraShortestPathConstraints()

		for dst in self.pdb.getDestinationSubnets() : 
			if dst in self.waypoints : 
				print dst, self.waypoints[dst], self.zeppelinPaths[dst]
				for path in self.zeppelinPaths[dst] :
					self.addWaypointComplianceConstraints(dst, path)


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

# nuZ3	
# maxSAT
# US Backbone, RocketFuelS