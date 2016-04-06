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
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(vtype=gb.GRB.INTEGER, name=str(sw1)+"-"+str(sw2))

				# Edge Weights are strictly positive
				#self.z3Solver.add(self.edgeWeights[sw1][sw2] > 0) 
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				#self.distvars[sw1][sw2] = Real(str(sw1)+":"+str(sw2))
				self.distvars[sw1][sw2] = self.ilpSolver.addVar(vtype=gb.GRB.INTEGER, name=str(sw1)+":"+str(sw2))
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

		for s in range(1, swCount + 1) : 
			for t in range(1, swCount + 1) : 
				print s,t, self.diamondPaths[s][t]
		print self.routefilters
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

		self.addDiamondConstraints()
		print "Solving ILP"
		solvetime = time.time()
		#modelsat = self.z3Solver.check()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime
		self.printProfilingStats()
		#self.topology.enableAllEdges()

		self.getEdgeWeightModel()		

		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.routefilters, self.distances)
		#self.topology.printWeights()

	def enforceDAGsAlgo(self, dags) :
		""" Algorithm to find edge weights for given dags """
		start_t = time.time()
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.edgeUsedFlag = [[False for x in range(swCount + 1)] for x in range(swCount + 1)]

		self.overlay = dict()
		self.destinationDAGs = dags
		for sw in range(1, swCount + 1) :
			self.overlay[sw] = []

		# Reset topology edge statuses
		self.topology.enableAllEdges()
		self.overlay()
		self.setUnusedEdgeWeights()

		end_t = time.time()
		print "Zeppelin: Time taken to algorithmically find edge weights is ", end_t - start_t

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

	def enforcePolicies(self): 
		start_t = time.time()
		self.initializeSMTVariables()

		self.synthesisSuccessFlag = self.enforceUnicastPolicies()

		end_t = time.time()
		#print "Time taken to solve the " + str(self.pdb.getPacketClassRange()) + " policies " + str(end_t - start_t)

		self.pdb.validatePolicies(self.topology)
		self.pdb.printPaths(self.topology)


		self.printProfilingStats()

	
	def addReachabilityPolicy(self, predicate, src, dst, waypoints=None, pathlen=None) :
		""" src = next hop switch of source host(s) 
			dst = next hop switch of destination host(s)
			W = Waypoint Set (list of nodes) 
			pathlen = Maxpath length of the path from source to destination"""

		# Translate s, d, W into logical topology numbers.
		srcSw = self.topology.getSwID(src)
		dstSw = self.topology.getSwID(dst)
		W = None
		if not waypoints == None :
			W = []
			for bag in waypoints :
				logicalBag = []
				for w in bag :
					logicalBag.append(self.topology.getSwID(w))
				W.append(logicalBag)

		# Add policy to PDB : 
		pc = self.pdb.addReachabilityPolicy(predicate, srcSw, dstSw, W, pathlen)
		return pc

	def addTrafficIsolationPolicy(self, policy1, policy2) : 
		# Isolation of traffic for Policies policy1 and policy2
		pc = self.pdb.addIsolationPolicy(policy1,policy2) 

	def addEqualMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		pc = self.pdb.addEqualMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	def addMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		pc = self.pdb.addMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	def addSwitchTablePolicy(self, swName, tableSize) :
		swID = self.topology.getSwID(swName)
		self.pdb.addSwitchTableConstraint(swID, tableSize)

	def addLinkCapacityPolicy(self, sw1, sw2, cap) :
		swID1 = self.topology.getSwID(sw1)
		swID2 = self.topology.getSwID(sw2)
		self.pdb.addLinkCapacityConstraint(swID1, swID2, cap)

	def enforceUnicastPolicies(self) :
		""" Enforcement of Policies stored in the PDB. """
		
		#dsts =  [4,5]
		self.z3Solver.push()
		# self.addDjikstraShortestPathConstraints()

		for pc in range(self.pdb.getPacketClassRange()) : 
			policy = self.pdb.getReachabilityPolicy(pc)
			self.addResilienceConstraints(src=policy[0][2], dst=policy[0][3], t_res=1) # Resilience = 1 is Reachability

		print self.toSMT2Benchmark(self.z3Solver, logic="QF_LRA")
		# for pno in range(self.pdb.getIsolationPolicyCount()) :
		# 	pc = self.pdb.getIsolationPolicy(pno)
		# 	self.addTrafficIsolationConstraints(pc[0], pc[1])

		solvetime = time.time()
		modelsat = self.z3Solver.check()
		self.z3solveTime += time.time() - solvetime

		if modelsat == z3.sat : 
			#print "Solver return SAT"
			self.fwdmodel = self.z3Solver.model()
			#self.getEdgeWeightModel()
		else :
			print "Input Policies not realisable"
			unsatCores = self.z3Solver.unsat_core()
			for unsatCore in unsatCores :
				print str(unsatCore)

		self.z3Solver.pop()

	def constructOverlayPaths(self) :
		""" Construct paths on overlay """

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
			if sw == dst : continue		
			
			# Add shortest path constraints for sw -> ... -> d
			self.ilpSolver.addConstr(self.dist(sw, dag[sw]) == self.ew(sw, dag[sw]))

			nextsw = dag[dag[sw]]
			while nextsw <> None :
				if self.getRank(sw, nextsw, dag[sw]) > 1 : 
					# Not shortest path in a diamond. Bypass intermediate distances
					swConv = nextsw
					nextsw = dag[nextsw]
					while nextsw <> None : 
						# Distance = Distance of diamond + rest of path
						self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, swConv) + self.dist(swConv, nextsw))
						nextsw = dag[nextsw]
					break
				
				self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, dag[sw]) + self.dist(dag[sw], nextsw))
			
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n <> dag[sw] : 
						self.ilpSolver.addConstr(self.dist(sw, nextsw) <= self.ew(sw, n) + self.dist(n, nextsw) - 1)

				nextsw = dag[nextsw]


	def addForwardingRuleConstraints(self, src, dst) :
		""" This function is only to be called if the flow src >> dst has other policies 
		like waypoints or isolation. For reachabilty, this is not required """
		if str(src) + ":" + str(dst) in self.fwdRulesMap : 
			return

		#print "Add Fwd rules for", src, dst

		swCount = self.topology.getSwitchCount()
		if str(src) + ":" + str(dst) not in self.resiliencevars : 
			return LookupError("Resilience variables not instantiated")
		resfwdvars = self.resiliencevars[str(src) + ":" + str(dst)][0]

		for sw1 in range(1, swCount + 1):
			if sw1 == dst : continue
			neighbours = self.topology.getSwitchNeighbours(sw1)

			for n in neighbours : 
				# Shortest Dist => Fwd(pc = 0)
				# PC = 0 is shortest path for src >> dst 
				self.z3Solver.add(Implies((self.dist(sw1, dst) == self.ew(sw1, n) + self.dist(n, dst)),
					resfwdvars[sw1][n][0]))
				self.z3Solver.add(Implies(resfwdvars[sw1][n][0], 
					(self.dist(sw1, dst) == self.ew(sw1, n) + self.dist(n, dst))))
				# Fwd(pc = 0) => Dist is implicitly implied by, but adding this make
				# synthesis faster though! : 
				# 1) rf => not fwd <=> fwd => not rf
				# 2) not rf => Path (from function addDjikstraShortestPathConstraints)

		self.fwdRulesMap[str(src) + ":" + str(dst)] = True

	def addResilienceConstraints(self, src, dst, t_res) : 
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()
		resfwdvars = [[[0 for x in range(t_res)] for x in range(swCount + 1)] for x in range(swCount + 1)]
		resreachvars = [[[0 for x in range(maxPathLen + 1)] for x in range(t_res)] for x in range(swCount + 1)]

		self.resiliencevars[str(src) + ":" + str(dst)] = [resfwdvars, resreachvars]
		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				for pc in range(t_res) :
					resfwdvars[sw1][sw2][pc] = Bool("res" + str(src) + "->" + str(dst) + ":" + str(sw1) + "-" + str(sw2) + ":" + str(pc))

		for sw1 in range(1,swCount+1):
			for pc in range(t_res) :
				for k in range(maxPathLen + 1) : 
					resreachvars[sw1][pc][k] = Bool("res" + str(src) + "->" + str(dst) + ":" + str(sw1) + ":" + str(pc) + ";" + str(k))

		# Route Filters disable forwarding.
		if not self.DISABLE_ROUTE_FILTERS : 
			for sw in range(1, swCount + 1):
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours :
					for pc in range(t_res) :
						self.z3Solver.add(Implies(self.rf(sw,n,dst), Not(resfwdvars[sw][n][pc])))

		self.addForwardingRuleConstraints(src,dst)
		# Path constraints for all the pcs. 
		
		for pc in range(t_res) :
			# Add constraints relating fwd to reach.
			for sw in range(1, swCount + 1): 
				if sw == src : continue
				for k in range(1, maxPathLen + 1) : 
					neighbours = self.topology.getSwitchNeighbours(sw)

					beforeHopAssertions = []
					for n in neighbours : 
						beforeHopAssert = And(resreachvars[n][pc][k-1], resfwdvars[n][sw][pc])
						beforeHopAssertions.append(beforeHopAssert)

					self.z3Solver.add(Implies(resreachvars[sw][pc][k], Or(*beforeHopAssertions)))

			# Distance 0 : 
			for sw in range(1, swCount + 1) : 
				if sw == src : 
					self.z3Solver.add(resreachvars[sw][pc][0])
				else : 
					self.z3Solver.add(Not(resreachvars[sw][pc][0]))

			# Destination is reachable.
			destAssertions = []
			for k in range(1, maxPathLen + 1) : 
				destAssertions.append(resreachvars[dst][pc][k])
			self.z3Solver.add(Or(*destAssertions))

			for n in self.topology.getSwitchNeighbours(dst) : 
				self.z3Solver.add(Not(resfwdvars[dst][n][pc]))

		# For k-resilience, k-edge disjoint paths required. 
		if t_res == 1 : 
			# No Resilience required.
			return
		for pc1 in range(t_res) : 
			for pc2 in range(pc1 + 1, t_res) : 
				for sw in range(1, swCount + 1):
					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						self.z3Solver.add( Not( And (resfwdvars[sw][n][pc1], resfwdvars[sw][n][pc2])) )
						self.z3Solver.add( Not( And (resfwdvars[sw][n][pc1], resfwdvars[n][sw][pc2])) )

		
	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes pc1 and pc2 """
		policy1 = self.pdb.getReachabilityPolicy(pc1)
		policy2 = self.pdb.getReachabilityPolicy(pc2)

		src1 = policy1[0][2]
		dst1 = policy1[0][3]
		src2 = policy2[0][2]
		dst2 = policy2[0][3]

		self.addForwardingRuleConstraints(src1,dst1)
		self.addForwardingRuleConstraints(src2,dst2)
		resfwdvars1 = self.resiliencevars[str(src1) + ":" + str(dst1)][0]
		resfwdvars2 = self.resiliencevars[str(src2) + ":" + str(dst2)][0]

		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1):
			neighbours = self.topology.getSwitchNeighbours(sw)
			for n in neighbours : 
				isolateAssert = Not( And (resfwdvars1[sw][n][0], resfwdvars2[sw][n][0]))
				self.z3Solver.add(isolateAssert)	

	def addPathConstraints(self, src, dst, path) :
		""" Add constraints to ensure path from <src> to <dst> is <path> """
		for i in range(len(path) - 1) :
			self.z3Solver.add(Not(self.rf(path[i], path[i+1], dst)))
			self.z3Solver(self.dist(path[i], dst) == self.ew(path[i], path[i+1]) + self.dist(path[i+1], dst))


	def getEdgeWeightModel(self) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) : 
				# ew_rat = self.fwdmodel.evaluate(self.ew(sw,n))
				# self.topology.addWeight(sw, n, float(ew_rat.numerator_as_long())/float(ew_rat.denominator_as_long()))
				ew = self.ew(sw, n).x
				self.topology.addWeight(sw, n, float(ew))

		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) :
				if s == t : continue
				self.distances[s][t] = self.dist(s,t).x

		
	def detectDiamonds(self) :
		""" Detecting diamonds in the different dags. A diamond is 
		defined as a subgraph of the overlay where there are two paths from s to t
		such that the two paths belong to different destination Dags. This implies that
		there are two shortest paths from s to t which is not enforceable with route filtering """
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		self.diamonds = []
		self.switchRanks = [[dict() for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.diamondPaths = [[dict() for x in range(swCount + 1)] for x in range(swCount + 1)]

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
									in1 = dstpath1.index(swConv)
									dstpath1 = dstpath1[:in1+1]
									dstpath1.insert(0, swDiv)
									in2 = dstpath2.index(swConv)
									dstpath2 = dstpath2[:in2+1]
									dstpath2.insert(0, swDiv)
									self.diamonds.append([dst1, dstpath1, dst2, dstpath2])
									self.diamondPaths[swDiv][swConv][dst1] = dstpath1 
									self.diamondPaths[swDiv][swConv][dst2] = dstpath2 
									break

		# for each src-dst pair diamond, ranks all paths according to length (shortest length has min rank)
		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					# Diamonds exists from s to t. Rank them by length
					diamonds = self.diamondPaths[s][t]
					ranks = dict()
					currRank = 1
					# All paths are not ranked
					while len(ranks) < len(diamonds) : 
						# Pick minimum length path
						minpath = range(100000)
						mindst = None
						for dst in diamonds : 
							path = diamonds[dst]
							if len(path) < len(minpath) and dst not in ranks :
								minpath = path
								mindst = dst
						# min path is least path without a rank
						ranks[mindst] = currRank
						currRank += 1
					# All paths are ranked. set up ranks of switches
					for dst in diamonds : 
						path = diamonds[dst]
						self.switchRanks[s][t][path[1]] = ranks[dst]

		self.generateRouteFilters()

	def getRank(self, s, t, nextsw) : 
		""" Rank of path from s to t via nextsw (which is neighbour of s """
		if nextsw in self.switchRanks[s][t] :
			return self.switchRanks[s][t][nextsw]
		else :
			# Not in a diamond, so shortest path
			return 1

	def addDiamondConstraints(self) :
		swCount = self.topology.getSwitchCount()
		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					# Diamonds exist. Add constraints to ensure path weights follow ranking
					diamonds = self.diamondPaths[s][t]
					for dst1 in diamonds :
						nextsw1= diamonds[dst1][1] # Neighbour of s
						rank1 = self.switchRanks[s][t][nextsw1]
						if rank1 > 1 : 
							# Not shortest path, therefore ensure path distance 
							# is strictly lesser than higher ranked paths from s to t
							for dst2 in diamonds : 
								nextsw2 = diamonds[dst2][1] # Neighbour of s
								rank2 = self.switchRanks[s][t][nextsw2] 
								if rank2 > rank1 :
									# Higher ranked path
									self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, nextsw2) + self.dist(nextsw2, t) - 1)


	def generateRouteFilters(self) :
		""" Disable lower ranked first edges of s in every s-t diamond for each destination"""
		swCount = self.topology.getSwitchCount()
		self.routefilters = dict()
		dsts = self.pdb.getDestinations()
		for dst in dsts : 
			self.routefilters[dst] = []

		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					# Diamonds exist. Add constraints to ensure path weights follow ranking
					diamonds = self.diamondPaths[s][t]
					for dst1 in diamonds :
						nextsw1= diamonds[dst1][1] # Neighbour of s
						rank1 = self.switchRanks[s][t][nextsw1] 
						for dst2 in diamonds : 
							nextsw2 = diamonds[dst2][1] # Neighbour of s
							rank2 = self.switchRanks[s][t][nextsw2] 
							if rank2 < rank1 : 
								# Lower ranked paths would be disabled
								self.routefilters[dst1].append([s, nextsw2])

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








# nuZ3
# maxSAT
# US Backbone, RocketFuelS