from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx
from subprocess import *
from collections import deque
import math
import gurobipy as gb
import copy

class ZeppelinSynthesiser(object) :
	def __init__(self, topology, pdb) :
		self.topology = topology
		self.pdb = pdb

		self.z3Solver = Solver()
		self.z3Solver.set(unsat_core=True)
		#self.z3Solver.set("sat.phase", "always-false")
		self.fwdmodel = None 
		
		# Route Filters
		self.DISABLE_ROUTE_FILTERS = True

		# Constraint Variables
		self.fwdRulesMap = dict()

		#SMT String file
		self.TO_SMT = True

		# Profiling Information.
		self.z3constraintTime = 0 # Time taken to create the constraints.
		self.z3addTime = 0 # Time taken to add the constraints.
		self.z3numberofadds = 0 # Count of adds.
		self.z3solveTime = 0 # Time taken to solve the constraints. 
		self.metisTime = 0	# Time taken to partition  the graphs.
		self.z3SolveCount = 0	# Count of z3 solve instances. 

		# ILP
		self.ilpSolver = gb.Model("C3")


	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distvars = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		#self.routefilters = [[[0 for x in range(swCount+1)] for x in range(swCount + 1)] for x in range(swCount + 1)]

		self.resiliencevars = dict()

		for sw1 in range(1,swCount+1):
			for sw2 in range(1,swCount+1):
				#self.edgeWeights[sw1][sw2] = Real(str(sw1)+"-"+str(sw2))
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(vtype=gb.GRB.CONTINUOUS, name=str(sw1)+"-"+str(sw2))

				# Edge Weights are strictly positive
				#self.z3Solver.add(self.edgeWeights[sw1][sw2] > 0) 
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				#self.distvars[sw1][sw2] = Real(str(sw1)+":"+str(sw2))
				self.distvars[sw1][sw2] = self.ilpSolver.addVar(vtype=gb.GRB.CONTINUOUS, name=str(sw1)+":"+str(sw2))
				# Distances also greater than 0

		self.ilpSolver.update()
		for sw1 in range(1,swCount+1):
			for sw2 in range(1,swCount+1):
				self.ilpSolver.addConstr(self.edgeWeights[sw1][sw2] >= 1)
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				self.ilpSolver.addConstr(self.distvars[sw1][sw2] >= 1) 

		# for sw1 in range(1,swCount+1):
		# 	for sw2 in range(1,swCount+1):
		# 		for sw3 in range(1,swCount + 1) :
					# self.routefilters[sw1][sw2][sw3] = Bool(str(sw1)+"!-!"+str(sw2) + ":" + str(sw3))
				

	def ew(self, sw1, sw2) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if sw2 not in neighbours : 
			raise LookupError("Weight for non-neighbours referred!")
		else : 
			return self.edgeWeights[sw1][sw2]

	def rf(self, sw1, sw2, sw3) :
		neighbours = self.topology.getSwitchNeighbours(sw2)
		if sw1 not in neighbours : 
			raise LookupError("Route Filter for non-neighbours referred!")
		else : 
			return self.routefilters[sw1][sw2][sw3]

	def dist(self, sw1, sw2) :
		if sw1 == sw2 : 
			return 0.0
		return self.distvars[sw1][sw2]

	def fwd(self, sw1, sw2, sw3) :
		if sw2 not in self.topology.getSwitchNeighbours(sw1) : 
			return False
		return self.fwdvars[sw1][sw2][sw3]

	def reach(self, sw1, sw2, sw3) :
		if sw1 == sw2 : return True
		return self.reachvars[sw1][sw2][sw3]

	def enforceDAGs(self, dags):
		""" Enforce the input destination dags """
		start_t = time.time()
		self.overlay = dict()
		self.destinationDAGs = dags
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()

		self.detectDiamonds() # Detect diamonds for route-filters
		self.initializeSMTVariables()

		for sw in range(1, swCount + 1) :
			self.overlay[sw] = []

		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw1 in dag :
				sw2 = dag[sw1] # Edge sw1 -> sw2
				if sw2 <> None : 
					if sw2 not in self.overlay[sw1] : 
						self.overlay[sw1].append(sw2)

		self.disableUnusedEdges()
		self.addDjikstraShortestPathConstraints()

		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag)

		#self.addDiamondConstraints()
		print "Solving ILP"
		solvetime = time.time()
		#modelsat = self.z3Solver.check()
		self.ilpSolver.optimize()
		# self.ilpSolver.computeIIS()
		# self.ilpSolver.write("model.ilp")
		self.z3solveTime += time.time() - solvetime
		self.printProfilingStats()
		self.topology.enableAllEdges()

		self.getEdgeWeightModel()		

		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.routefilters, self.distances)
		#self.topology.printWeights()

	# def enforceDAGsAlgo(self, dags) :
	# 	""" Algorithm to find edge weights for given dags """
	# 	start_t = time.time()
	# 	swCount = self.topology.getSwitchCount()

	# 	self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
	# 	self.edgeUsedFlag = [[False for x in range(swCount + 1)] for x in range(swCount + 1)]

	# 	self.overlay = dict()
	# 	self.destinationDAGs = dags
	# 	for sw in range(1, swCount + 1) :
	# 		self.overlay[sw] = []

	# 	# Reset topology edge statuses
	# 	self.topology.enableAllEdges()
	# 	self.overlay()
	# 	self.setUnusedEdgeWeights()

	# 	end_t = time.time()
	# 	print "Zeppelin: Time taken to algorithmically find edge weights is ", end_t - start_t

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

	# def enforcePolicies(self): 
	# 	start_t = time.time()
	# 	self.initializeSMTVariables()

	# 	self.synthesisSuccessFlag = self.enforceUnicastPolicies()

	# 	end_t = time.time()
	# 	#print "Time taken to solve the " + str(self.pdb.getPacketClassRange()) + " policies " + str(end_t - start_t)

	# 	self.pdb.validatePolicies(self.topology)
	# 	self.pdb.printPaths(self.topology)


	# 	self.printProfilingStats()

	
	# def addReachabilityPolicy(self, predicate, src, dst, waypoints=None, pathlen=None) :
	# 	""" src = next hop switch of source host(s) 
	# 		dst = next hop switch of destination host(s)
	# 		W = Waypoint Set (list of nodes) 
	# 		pathlen = Maxpath length of the path from source to destination"""

	# 	# Translate s, d, W into logical topology numbers.
	# 	srcSw = self.topology.getSwID(src)
	# 	dstSw = self.topology.getSwID(dst)
	# 	W = None
	# 	if not waypoints == None :
	# 		W = []
	# 		for bag in waypoints :
	# 			logicalBag = []
	# 			for w in bag :
	# 				logicalBag.append(self.topology.getSwID(w))
	# 			W.append(logicalBag)

	# 	# Add policy to PDB : 
	# 	pc = self.pdb.addReachabilityPolicy(predicate, srcSw, dstSw, W, pathlen)
	# 	return pc

	# def addTrafficIsolationPolicy(self, policy1, policy2) : 
	# 	# Isolation of traffic for Policies policy1 and policy2
	# 	pc = self.pdb.addIsolationPolicy(policy1,policy2) 

	# def addEqualMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
	# 	pc = self.pdb.addEqualMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	# def addMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
	# 	pc = self.pdb.addMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	# def addSwitchTablePolicy(self, swName, tableSize) :
	# 	swID = self.topology.getSwID(swName)
	# 	self.pdb.addSwitchTableConstraint(swID, tableSize)

	# def addLinkCapacityPolicy(self, sw1, sw2, cap) :
	# 	swID1 = self.topology.getSwID(sw1)
	# 	swID2 = self.topology.getSwID(sw2)
	# 	self.pdb.addLinkCapacityConstraint(swID1, swID2, cap)

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
		dsts = self.pdb.getDestinations()

		#print "number of destinations", len(dsts)
		for src in range(1, swCount + 1):
			if self.topology.isSwitchDisabled(src) :
				continue
			for dst in range(1, swCount + 1) :
				if self.topology.isSwitchDisabled(dst) :
					continue
				if src == dst : 
					continue
				# if not self.topology.isConnected(src, dst) :
				# 	continue # src, dst is not connected in overlay, distance(src, dst) does not matter

				for sw in range(1, swCount + 1) :
					if sw == src or sw == dst : continue 
					if self.topology.isSwitchDisabled(sw) : 
						continue

					self.ilpSolver.addConstr(self.dist(src, dst) <= self.dist(src, sw) + self.dist(sw, dst))	

	def addDestinationDAGConstraints(self, dst, dag) :
		""" Adds constraints such that dag weights are what we want them to be """
		
		for sw in dag : 
			# if self.isDiamondSource(sw) : 
			# 	# Add Diamonds constraints in addDiamondConstraints.
			# 	nextsw = dag[sw]
			# 	diamondDst = None
			# 	while nextsw <> None:
			# 		if self.isDiamondDestination(nextsw) : 
			# 			diamondDst = nextsw
			# 		if diamondDst == None : 
			# 			self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, dag[sw]) + self.dist(dag[sw], nextsw))
			# 			# Strict inequality
			# 			neighbours = self.topology.getSwitchNeighbours(sw)
			# 			for n in neighbours : 
			# 				if n <> dag[sw] : 
			# 					self.ilpSolver.addConstr(self.dist(sw, nextsw) <= self.ew(sw, n) + self.dist(n, nextsw) - 1)
			# 		else : 
			# 			self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, diamondDst) + self.dist(diamondDst, nextsw))
			# 		nextsw = dag[nextsw]
			# 	continue
			nextsw = dag[sw]
			while nextsw <> None :				
				if nextsw == dag[sw] :
					self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.ew(sw, dag[sw]))
				else : 
					self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, dag[sw]) + self.dist(dag[sw], nextsw))
			
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n <> dag[sw] : 
						self.ilpSolver.addConstr(self.dist(sw, nextsw) <= self.ew(sw, n) + self.dist(n, nextsw) - 1)

				nextsw = dag[nextsw]

	def getEdgeWeightModel(self) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) : 
				if n not in self.overlay[sw] :
					self.topology.addWeight(sw, n, float(1000))
					#print sw, n, 1000
				else : 
				# ew_rat = self.fwdmodel.evaluate(self.ew(sw,n))
				# self.topology.addWeight(sw, n, float(ew_rat.numerator_as_long())/float(ew_rat.denominator_as_long()))
					ew = self.ew(sw, n).x
					if float(ew) > 1000 : 
						ew = 1000
					self.topology.addWeight(sw, n, float(ew))
					#print sw, n, float(ew)

		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) :
				if s == t : continue
				self.distances[s][t] = self.dist(s,t).x
				#print s,t, self.distances[s][t]

	def detectDiamonds(self, onlyDetect=False) :
		""" Detecting diamonds in the different dags. A diamond is 
		defined as a subgraph of the overlay where there are two paths from s to t
		such that the two paths belong to different destination Dags. This implies that
		there are two shortest paths from s to t which is not enforceable with route filtering """
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		self.dstDiamonds = dict()
		self.switchRanks = [[dict() for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.diamondPaths = [[dict() for x in range(swCount + 1)] for x in range(swCount + 1)]
		
		# Diamond dependencies
		self.dependencyFlag = dict()
		self.dependencyList = dict()
		self.subsets = dict()
		self.supersets = dict()
		
		for dst in dsts : 
			self.dstDiamonds[dst] = []

		for dst1 in dsts :
			for dst2 in dsts : 
				if dst1 >= dst2 : continue 
				dag1 = self.destinationDAGs[dst1]
				dag2 = self.destinationDAGs[dst2]

				for swDiv in dag1 : 
					if swDiv == dst1 or swDiv == dst2 : continue 
					# Detect a diamond
					if swDiv in dag2 : 
						# swDiv in the dag. Check if both dags diverge
						if dag1[swDiv] <> dag2[swDiv] : 
							# Diverging common switches, search for intersecting switch
							dstpath1 = [dag1[swDiv]]
							nextsw = dag1[dag1[swDiv]]
							while nextsw <> None:
								dstpath1.append(nextsw)
								nextsw = dag1[nextsw]
							dstpath2 = [dag2[swDiv]]
							nextsw = dag2[dag2[swDiv]]
							while nextsw <> None:
								dstpath2.append(nextsw)
								nextsw = dag2[nextsw]
							# dstpath1 and dstpath2 are paths from sw to their respective destinations
							# Find intersection

							for swConv in dstpath1 : 
								if swConv in dstpath2 : 
									# Intersection! This is the smallest diamond starting at sw
									
									# If diamond detection mode, return True, as Diamond as been detected
									if onlyDetect :
										print dst1, dst2, swDiv, swConv
 										return True

									in1 = dstpath1.index(swConv)
									dstpath1 = dstpath1[:in1+1]
									dstpath1.insert(0, swDiv)
									in2 = dstpath2.index(swConv)
									dstpath2 = dstpath2[:in2+1]
									dstpath2.insert(0, swDiv)

									exists = False
									for dst in self.diamondPaths[swDiv][swConv] :
										if self.diamondPaths[swDiv][swConv][dst] == dstpath1 and dst <> dst1 :
											# dstpath1's diamond already exists, ignore. 
											exists = True
											break
									if not exists : 
										self.diamondPaths[swDiv][swConv][dst1] = dstpath1 

									if dstpath1 not in self.dstDiamonds[dst1] : 
										self.dstDiamonds[dst1].append(dstpath1)

									exists = False
									for dst in self.diamondPaths[swDiv][swConv] :
										if self.diamondPaths[swDiv][swConv][dst] == dstpath2 and dst <> dst2 :
											# dstpath1's diamond already exists, ignore. 
											exists = True
											break

									if not exists : 
										self.diamondPaths[swDiv][swConv][dst2] = dstpath2

									if dstpath2 not in self.dstDiamonds[dst2] : 
										self.dstDiamonds[dst2].append(dstpath2)
									break

		if onlyDetect : 
			return False # If diamond was detected, then return value would be inside the loop itself

		# Assign ranks
		for dst in self.dstDiamonds : 
			diamondpaths = self.dstDiamonds[dst]
			for dpath1 in diamondpaths : 
				for dpath2 in diamondpaths : 
					if dpath1 == dpath2 : continue
					if len(dpath1) >= len(dpath2) : continue 
					# check if dpath1 completely in dpath2
					start = dpath1[0]
					end = dpath1[len(dpath1) - 1]
					if start in dpath2 and end in dpath2 : 
						# From this and condition 2 (dpath1 < dpath2), dpath1 is strict subpath of dpath2
						self.addDependency(dpath1, dpath2, dst)

		totalRanks = 0
		for s in range(1, swCount + 1) : 
			for t in range(1, swCount + 1) : 
				totalRanks += len(self.diamondPaths[s][t])

		print "Finding ranks"
		assignedRanks = 0
		while assignedRanks < totalRanks :
			# Find a suitable source-dst pair to assign ranks
			for s in range(1, swCount + 1) : 
				for t in range(1, swCount + 1) : 
					if len(self.diamondPaths[s][t]) > 0 and len(self.switchRanks[s][t]) <> len(self.diamondPaths[s][t]): 
						subsetOnlyEdges = []
						supersetOnlyEdges = []
						unConstrainedEdges = []
						assignedEdges = []
						diamonds = self.diamondPaths[s][t]
						for dst in diamonds : 
							path = diamonds[dst]
							if self.isUnconstrained(path, dst) : 
								unConstrainedEdges.append(path[1])
							elif self.isSubsetOnly(path, dst) : 
								subsetOnlyEdges.append(path[1])
							elif path[1] in self.switchRanks[s][t] : 
								assignedEdges.append(path[1])
							elif self.isSupersetOnly(path, dst) : 
								supersetOnlyEdges.append(path[1])
							
						print s,t, subsetOnlyEdges, supersetOnlyEdges, unConstrainedEdges, assignedEdges
						print diamonds, self.switchRanks[s][t], len(self.switchRanks[s][t]), len(self.diamondPaths[s][t])

						if len(subsetOnlyEdges) + len(unConstrainedEdges) + len(assignedEdges) == len(diamonds) : 
							# Largest Diamond. Set Ranks at will
							if len(assignedEdges) > 1 : 
								print "Not possible, error"
								exit(0)
							elif len(assignedEdges) == 1 : 
								currRank = 2
							else : 
								currRank = 1
							for n in unConstrainedEdges :
								self.switchRanks[s][t][n] = currRank
								currRank += 1
								assignedRanks += 1
							for n in subsetOnlyEdges : 
								self.switchRanks[s][t][n] = currRank
								if currRank == 1 : 
									# Need to make sure the subset paths are set to 1
									for dst in diamonds : 
										path = diamonds[dst]
										if path[1] == n : 
											dependencies = self.getDependencies(path, dst)
											for dpath in dependencies : 
												if dpath[1] not in self.switchRanks[dpath[0]][dpath[len(dpath) - 1]] : 
													self.switchRanks[dpath[0]][dpath[len(dpath) - 1]][dpath[1]] = 1 # Cannot be lower ranked 
													assignedRanks += 1
												elif dpath[1] in self.switchRanks[dpath[0]][dpath[len(dpath) - 1]] : 
													if self.switchRanks[dpath[0]][dpath[len(dpath) - 1]][dpath[1]] > 1 : 
														print "Violation of invariant!" 
														exit(0)
								if currRank > 1 : 
									# Can remove dependencies of smaller paths
									for dst in diamonds : 
										path = diamonds[dst]
										if path[1] == n : 
											self.removeDependencies(path, dst)
								currRank += 1
								assignedRanks += 1	
						if len(supersetOnlyEdges) + len(unConstrainedEdges) + len(subsetOnlyEdges) == len(diamonds) and len(supersetOnlyEdges) == 1 :
							# Set the superset Edge to rank 1 (no contradtictions)
							currRank = 1
							for n in supersetOnlyEdges : 
								self.switchRanks[s][t][n] = currRank 
								assignedRanks += 1
								currRank += 1
								for dst in diamonds : 
									path = diamonds[dst]
									if path[1] == n : 
										self.removeDependencies(path, dst)
							for n in subsetOnlyEdges : 
								self.switchRanks[s][t][n] = currRank 
								assignedRanks += 1
								currRank += 1
								for dst in diamonds : 
									path = diamonds[dst]
									if path[1] == n : 
										self.removeDependencies(path, dst)
							for n in unConstrainedEdges :
								self.switchRanks[s][t][n] = currRank
								currRank += 1
								assignedRanks += 1


		print "Found ranks"
		self.modifyDAGs()
		self.generateRouteFilters() 
	
	def addDependency(self, path1, path2, dst) : 
		""" Diamonds: path1 is a subpath of path2 in dag of dst"""
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)

		s2 = path2[0]
		t2 = path2[len(path2) - 1]
		key2 = str(s2) + "-" + str(t2) + ":" + str(dst)

		# Dependent diamond paths
		self.dependencyFlag[key1] = True
		self.dependencyFlag[key2] = True 
			
		if key1 in self.dependencyList : 
			self.dependencyList[key1].append(path2)
		else : 
			self.dependencyList[key1] = [path2]

		if key2 in self.dependencyList : 
			self.dependencyList[key2].append(path1)
		else : 
			self.dependencyList[key2] = [path1]

	def getDependencies(self, path1, dst) : 
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
		if key1 in self.dependencyList : 
			return self.dependencyList[key1]
		else : 
			return []

	def isUnconstrained(self, path1, dst) :
		""" Returns if path1's rank is not dependent with any other path rank"""
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
		if key1 in self.dependencyFlag :
			return False
		else :
			return True 

	def isSubsetOnly(self, path1, dst) :
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
		if key1 not in self.dependencyList : return False
		dpaths = self.dependencyList[key1]
		for dpath in dpaths : 
			if dpath[0] not in path1 or dpath[len(dpath) - 1] not in path1 :
				return False
		return True 

	def isSupersetOnly(self, path1, dst) :
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
		if key1 not in self.dependencyList : return False
		dpaths = self.dependencyList[key1]
		for dpath in dpaths : 
			if path1[0] not in dpath or path1[len(path1) - 1] not in dpath :
				return False
		return True 

	def removeDependencies(self, path1, dst) :
		""" Removes dependencies of all paths subset of path as path is not sp"""
		s1 = path1[0]
		t1 = path1[len(path1) - 1]
		key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
		dpaths = self.dependencyList[key1]
		self.dependencyList[key1] = []
		del self.dependencyFlag[key1]

		for dpath in dpaths : 
			s2 = dpath[0]
			t2 = dpath[len(dpath) - 1]
			key2 = str(s2) + "-" + str(t2) + ":" + str(dst)
			dpaths2 = self.dependencyList[key2]
			newdpaths2 = []
			for dpath2 in dpaths2 : 
				if dpath2 <> path1 :
					newdpaths2.append(dpath2)
			if len(newdpaths2) == 0 :
				# Unconstrained 
				self.dependencyList[key2] = []
				del  self.dependencyFlag[key2]
			else : 
				self.dependencyList[key2] = newdpaths2

	def getRank(self, s, t, nextsw) : 
		""" Rank of path from s to t via nextsw (which is neighbour of s """
		if nextsw in self.switchRanks[s][t] :
			return self.switchRanks[s][t][nextsw]
		elif len(self.switchRanks[s][t]) > 0 :
			# There exists a diamond from s-t, but nextsw not in any diamond paths. Return a high rank
			return 10000
		else :
			# No diamonds from s-t. Shortest Path
			return 1

	def isDiamondSource(self, s) :
		swCount = self.topology.getSwitchCount()
		for t in range(1, swCount + 1) :
			if len(self.switchRanks[s][t]) > 0 :
				return True
		return False

	def isDiamondDestination(self, t) :
		swCount = self.topology.getSwitchCount()
		for s in range(1, swCount + 1) :
			if len(self.switchRanks[s][t]) > 0 :
				return True
		return False

	def addDiamondConstraints(self) :
		swCount = self.topology.getSwitchCount()
		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					# Diamonds exist. Add constraints to ensure path weights follow ranking
					diamonds = self.diamondPaths[s][t]
					diamondNeighbours = []
					neighbours = self.topology.getSwitchNeighbours(s)
					print s,t, diamonds, "is a diamond"
					for dst1 in diamonds :
						nextsw1= diamonds[dst1][1] # Neighbour of s
						diamondNeighbours.append(nextsw1)
						rank1 = self.switchRanks[s][t][nextsw1]
						if rank1 == 1 : 
							print diamonds[dst1]
							# Shortest path from s to t is through nextsw1
							self.ilpSolver.addConstr(self.dist(s,t) == self.dist(s, nextsw1) + self.dist(nextsw1, t))
					
							print neighbours, s,t, "I am here!", rank1
							for n in neighbours : 
								if self.getRank(s,t,n) > rank1 : 
									print nextsw1, n, self.getRank(s,t,n)
									# Higher ranked path should be strictly greater in distance
									self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, n) + self.dist(n, t) - 1)

						# for dst2 in diamonds : 
						# 	nextsw2 = diamonds[dst2][1] # Neighbour of s
						# 	rank2 = self.switchRanks[s][t][nextsw2] 
						# 	if rank2 > rank1 :
						# 		# Higher ranked path
						# 		self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, nextsw2) + self.dist(nextsw2, t) - 1)


					#Constraints to ensure highest rank path is shorter than other non-ranked paths
					
					# neighbours = self.topology.getSwitchNeighbours(s)
					# for dst1 in diamonds :
					# 	nextsw1= diamonds[dst1][1] # Neighbour of s
					# 	rank1 = self.switchRanks[s][t][nextsw1]
					# 	if rank1 == len(diamonds) :
					# 		# Highest Rank Path
					# 		for n in neighbours : 
					# 			if n not in diamondNeighbours : 
					# 				self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, n) + self.dist(n, t) - 1)


	def modifyDAGs(self) :
		self.unmodifiedDestinationDAGs = copy.deepcopy(self.destinationDAGs)
		swCount = self.topology.getSwitchCount()
		self.routefilters = dict()
		dsts = self.pdb.getDestinations()

		# Initialize route filters to the empty set
		for dst in dsts : 
			self.routefilters[dst] = []

		for s in range(1, swCount + 1) :
			diamondDsts = []
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					diamondDsts.append(t)

			if len(diamondDsts) < 1 : continue # No diamonds.			
			elif len(diamondDsts) == 1 : 
				# Only one diamond, can modify DAGs
				t = diamondDsts[0] 
				diamonds = self.diamondPaths[s][t]
				for dst1 in diamonds :
					spath = diamonds[dst1]
					nextsw1 = spath[1] # Neighbour of s
					rank1 = self.switchRanks[s][t][nextsw1] 
					
					if rank1 == 1 : 
						for dst2 in diamonds : 
							if dst2 <> dst1 : 
								# Rank > 1. Reroute s to spath
								path2 = diamonds[dst2]
								# Rerouting
								self.reroute(dst2, path2, spath)

			else : 	
				# More than one diamond at source. 
				# If a destination DAG has to be rerouted along multiple paths
				# (It is a lower ranked path in two diamonds) 
				# => Reroute along longer path.
				rerouteDstPaths = dict()
				for t in diamondDsts : 
					diamonds =  self.diamondPaths[s][t]
					firstRankPath = self.getFirstRankPath(s,t)
					for dst1 in diamonds : 
						path1 = diamonds[dst1]
						rank1 = self.switchRanks[s][t][path1[1]]
						diamondDsts = [] # Destinations sharing diamond path <path1>
						if rank1 > 1 :
							for dst2 in dsts : 
								if path1 in self.dstDiamonds[dst2] and dst2 not in diamondDsts : 
									diamondDsts.append(dst2)

							for dst2 in diamondDsts : 
							# Higher ranked path, needs rerouting
								if dst2 not in rerouteDstPaths :
									rerouteDstPaths[dst2] = [[path1, firstRankPath]]
								else : 
									rerouteDstPaths[dst2].append([path1, firstRankPath])

				for dst1 in rerouteDstPaths : 
					if len(rerouteDstPaths[dst1]) >= 1 : 
						# Part of multiple diamonds, reroute to longest first rank path
						# Sort by path length, and reroute depending on largest diamond
						rerouteDstPaths[dst1] = sorted(rerouteDstPaths[dst1], key=lambda p: len(p[0]), reverse=True) 
						# First element of the list will have the longest diamond path for dst
						path1 = rerouteDstPaths[dst1][0][0]
						spath = rerouteDstPaths[dst1][0][1]
						self.reroute(dst1, path1, spath)

		print self.detectDiamonds(onlyDetect=True), " is Diamonds still here?"

	def reroute(self, rdst, path, spath) :
		""" Reroute all dsts using path to spath """ 

		dag = self.destinationDAGs[rdst]
		# Start from s and send dag2 traffic through the largest
		# subpath of <spath>
		dag[spath[0]] = spath[1] 
		for i in range(1, len(spath) - 1) : 
			if spath[i] not in dag : 
				dag[spath[i]] = spath[i + 1]
			else :
				# Switch in dag2 
				break 

	def getFirstRankPath(self, s, t) : 
		diamonds = self.diamondPaths[s][t]
		for dst in diamonds : 
			path = diamonds[dst]
			rank = self.switchRanks[s][t][path[1]]
			if rank == 1 : 
				return path

	def generateRouteFilters(self) :
		""" Disable lower ranked first edges of s in every s-t diamond for each destination"""
		swCount = self.topology.getSwitchCount()
		self.routefilters = dict()
		dsts = self.pdb.getDestinations()

		print self.routefilters

	# Profiling Statistics : 
	def printProfilingStats(self) :
		#print "Time taken to add constraints are ", self.z3addTime
		print "Zeppelin: Time taken to solve constraints are ", self.z3solveTime
		# print "Number of z3 adds to the solver are ", self.z3numberofadds

	def toSMT2Benchmark(self, f, status="unknown", name="benchmark", logic=""):
		v = (Ast * 0)()
		if isinstance(f, Solver):
			a = f.assertions()
			if len(a) == 0:
				f = BoolVal(True)
			else:
				f = And(*a)
			return Z3_benchmark_to_smtlib_string(f.ctx_ref(), name, logic, status, "", 0, v, f.as_ast())




		# for each src-dst pair diamond, ranks all paths according to length (shortest length has min rank)
		# for s in range(1, swCount + 1) :
		# 	diamondDsts = []
		# 	for t in range(1, swCount + 1) : 
		# 		if len(self.diamondPaths[s][t]) > 0 : 
		# 			diamondDsts.append(t)
		# 	if len(diamondDsts) == 0 : continue # No diamonds starting at source
		# 	else : 
		# 		# Rank all neighbours of s randomly
		# 		neighbours = self.topology.getSwitchNeighbours(s)
		# 		sRanks = dict()
		# 		currRank = 1
		# 		for n in neighbours : 
		# 			sRanks[n] = currRank
		# 			currRank += 1

		# 		# Number of diamonds from s is greater than 1
		# 		# If two diamonds with same source share a edge, if edge is ranked one
		# 		# in one of the diamonds, it has to be ranked one in the other as well.
				
		# 		for t in diamondDsts : 
		# 			diamonds = self.diamondPaths[s][t]
		# 			ranks = dict()
		# 			currRank = 1
		# 			while len(ranks) < len(diamonds):
		# 				minRank = 100000
		# 				minNeighbour = None 
		# 				for dst in diamonds : 
		# 					path = diamonds[dst]
		# 					if path[1] not in ranks and sRanks[path[1]] < minRank : 
		# 						minNeighbour = path[1]
		# 						minRank = sRanks[minNeighbour]
		# 				ranks[minNeighbour] = currRank
		# 				currRank += 1					
		# 			for n in ranks : 
		# 				self.switchRanks[s][t][n] = ranks[n]

		# for t in range(1, swCount + 1) :
		# 	diamondSrcs = []
		# 	for s in range(1, swCount + 1) :
		# 		if len(self.diamondPaths[s][t]) > 0 : 
		# 			diamondSrcs.append(s)
		# 	if len(diamondSrcs)	 > 0 : 
		# 		print t, diamondSrcs	

	# def addForwardingRuleConstraints(self, src, dst) :
	# 	""" This function is only to be called if the flow src >> dst has other policies 
	# 	like waypoints or isolation. For reachabilty, this is not required """
	# 	if str(src) + ":" + str(dst) in self.fwdRulesMap : 
	# 		return

	# 	#print "Add Fwd rules for", src, dst

	# 	swCount = self.topology.getSwitchCount()
	# 	if str(src) + ":" + str(dst) not in self.resiliencevars : 
	# 		return LookupError("Resilience variables not instantiated")
	# 	resfwdvars = self.resiliencevars[str(src) + ":" + str(dst)][0]

	# 	for sw1 in range(1, swCount + 1):
	# 		if sw1 == dst : continue
	# 		neighbours = self.topology.getSwitchNeighbours(sw1)

	# 		for n in neighbours : 
	# 			# Shortest Dist => Fwd(pc = 0)
	# 			# PC = 0 is shortest path for src >> dst 
	# 			self.z3Solver.add(Implies((self.dist(sw1, dst) == self.ew(sw1, n) + self.dist(n, dst)),
	# 				resfwdvars[sw1][n][0]))
	# 			self.z3Solver.add(Implies(resfwdvars[sw1][n][0], 
	# 				(self.dist(sw1, dst) == self.ew(sw1, n) + self.dist(n, dst))))
	# 			# Fwd(pc = 0) => Dist is implicitly implied by, but adding this make
	# 			# synthesis faster though! : 
	# 			# 1) rf => not fwd <=> fwd => not rf
	# 			# 2) not rf => Path (from function addDjikstraShortestPathConstraints)

	# 	self.fwdRulesMap[str(src) + ":" + str(dst)] = True

	# def addResilienceConstraints(self, src, dst, t_res) : 
	# 	swCount = self.topology.getSwitchCount()
	# 	maxPathLen = self.topology.getMaxPathLength()
	# 	resfwdvars = [[[0 for x in range(t_res)] for x in range(swCount + 1)] for x in range(swCount + 1)]
	# 	resreachvars = [[[0 for x in range(maxPathLen + 1)] for x in range(t_res)] for x in range(swCount + 1)]

	# 	self.resiliencevars[str(src) + ":" + str(dst)] = [resfwdvars, resreachvars]
	# 	for sw1 in range(1,swCount+1):
	# 		for sw2 in range(1, swCount + 1) :
	# 			for pc in range(t_res) :
	# 				resfwdvars[sw1][sw2][pc] = Bool("res" + str(src) + "->" + str(dst) + ":" + str(sw1) + "-" + str(sw2) + ":" + str(pc))

	# 	for sw1 in range(1,swCount+1):
	# 		for pc in range(t_res) :
	# 			for k in range(maxPathLen + 1) : 
	# 				resreachvars[sw1][pc][k] = Bool("res" + str(src) + "->" + str(dst) + ":" + str(sw1) + ":" + str(pc) + ";" + str(k))

	# 	# Route Filters disable forwarding.
	# 	if not self.DISABLE_ROUTE_FILTERS : 
	# 		for sw in range(1, swCount + 1):
	# 			neighbours = self.topology.getSwitchNeighbours(sw)
	# 			for n in neighbours :
	# 				for pc in range(t_res) :
	# 					self.z3Solver.add(Implies(self.rf(sw,n,dst), Not(resfwdvars[sw][n][pc])))

	# 	self.addForwardingRuleConstraints(src,dst)
	# 	# Path constraints for all the pcs. 
		
	# 	for pc in range(t_res) :
	# 		# Add constraints relating fwd to reach.
	# 		for sw in range(1, swCount + 1): 
	# 			if sw == src : continue
	# 			for k in range(1, maxPathLen + 1) : 
	# 				neighbours = self.topology.getSwitchNeighbours(sw)

	# 				beforeHopAssertions = []
	# 				for n in neighbours : 
	# 					beforeHopAssert = And(resreachvars[n][pc][k-1], resfwdvars[n][sw][pc])
	# 					beforeHopAssertions.append(beforeHopAssert)

	# 				self.z3Solver.add(Implies(resreachvars[sw][pc][k], Or(*beforeHopAssertions)))

	# 		# Distance 0 : 
	# 		for sw in range(1, swCount + 1) : 
	# 			if sw == src : 
	# 				self.z3Solver.add(resreachvars[sw][pc][0])
	# 			else : 
	# 				self.z3Solver.add(Not(resreachvars[sw][pc][0]))

	# 		# Destination is reachable.
	# 		destAssertions = []
	# 		for k in range(1, maxPathLen + 1) : 
	# 			destAssertions.append(resreachvars[dst][pc][k])
	# 		self.z3Solver.add(Or(*destAssertions))

	# 		for n in self.topology.getSwitchNeighbours(dst) : 
	# 			self.z3Solver.add(Not(resfwdvars[dst][n][pc]))

	# 	# For k-resilience, k-edge disjoint paths required. 
	# 	if t_res == 1 : 
	# 		# No Resilience required.
	# 		return
	# 	for pc1 in range(t_res) : 
	# 		for pc2 in range(pc1 + 1, t_res) : 
	# 			for sw in range(1, swCount + 1):
	# 				neighbours = self.topology.getSwitchNeighbours(sw)
	# 				for n in neighbours : 
	# 					self.z3Solver.add( Not( And (resfwdvars[sw][n][pc1], resfwdvars[sw][n][pc2])) )
	# 					self.z3Solver.add( Not( And (resfwdvars[sw][n][pc1], resfwdvars[n][sw][pc2])) )

		
	# def addTrafficIsolationConstraints(self, pc1, pc2) : 
	# 	""" Adding constraints for Isolation Policy enforcement of traffic for packet classes pc1 and pc2 """
	# 	policy1 = self.pdb.getReachabilityPolicy(pc1)
	# 	policy2 = self.pdb.getReachabilityPolicy(pc2)

	# 	src1 = policy1[0][2]
	# 	dst1 = policy1[0][3]
	# 	src2 = policy2[0][2]
	# 	dst2 = policy2[0][3]

	# 	self.addForwardingRuleConstraints(src1,dst1)
	# 	self.addForwardingRuleConstraints(src2,dst2)
	# 	resfwdvars1 = self.resiliencevars[str(src1) + ":" + str(dst1)][0]
	# 	resfwdvars2 = self.resiliencevars[str(src2) + ":" + str(dst2)][0]

	# 	swCount = self.topology.getSwitchCount()
	# 	for sw in range(1, swCount + 1):
	# 		neighbours = self.topology.getSwitchNeighbours(sw)
	# 		for n in neighbours : 
	# 			isolateAssert = Not( And (resfwdvars1[sw][n][0], resfwdvars2[sw][n][0]))
	# 			self.z3Solver.add(isolateAssert)	

	# def addPathConstraints(self, src, dst, path) :
	# 	""" Add constraints to ensure path from <src> to <dst> is <path> """
	# 	for i in range(len(path) - 1) :
	# 		self.z3Solver.add(Not(self.rf(path[i], path[i+1], dst)))
	# 		self.z3Solver(self.dist(path[i], dst) == self.ew(path[i], path[i+1]) + self.dist(path[i+1], dst))



# nuZ3
# maxSAT
# US Backbone, RocketFuelS