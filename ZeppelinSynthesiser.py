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
from collections import defaultdict

class ZeppelinSynthesiser(object) :
	def __init__(self, topology, pdb) :
		self.topology = topology
		self.pdb = pdb

		self.fwdmodel = None 
		
		# Route Filters
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

		self.routefilters = dict()
		
		self.sums = []
		# Resilience 
		self.t_res = 2


	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 
		self.routefiltersVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.maxFlowVars = defaultdict(lambda:defaultdict(lambda:None))

		dsts = self.pdb.getDestinations()

		for sw1 in range(1,swCount+1):
			for sw2 in self.topology.getSwitchNeighbours(sw1) :
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=1.00, ub=10000, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + " ")

		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=0.00, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + " ")
				# for dst in dsts : 
				# 	self.distVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00,vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2)+"-"+str(dst) + " ")

		for endpt in self.endpoints : 
			for sw2 in self.topology.getSwitchNeighbours(endpt[0]) : 
				self.routefiltersVars[endpt[0]][sw2][endpt[1]] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS, name="RF" + "-" + str(endpt[0])+"-"+str(sw2)+"-"+str(endpt[1]))

		# for sw1 in range(1,swCount+1):
		# 	for sw2 in range(1,swCount+1):
		# 		for dst in dsts:
		# 			self.routefiltersVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.BINARY, name="RF" + "-" + str(sw1)+":"+str(sw2)+"-"+str(dst))
		

		self.ilpSolver.update()

	def ew(self, sw1, sw2) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if sw2 not in neighbours : 
			raise LookupError("Weight for non-neighbours referred!")
		else : 
			return self.edgeWeights[sw1][sw2]

	def rf(self, sw1, sw2, dst) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if [sw1, dst] not in self.endpoints : 
			raise LookupError("Non existent Route Filter variable referred!")
		if sw2 not in neighbours : 
			raise LookupError("Route Filter for non-neighbours referred!")
		else : 
			return self.routefiltersVars[sw1][sw2][dst]

	def dist(self, sw1, sw2, dst=0) : 
		# Default value of dst = 0
		if sw1 == sw2 : 
			return 0.0
		return self.distVars[sw1][sw2][dst]

	def enforceDAGs(self, dags, endpoints):
		""" Enforce the input destination dags """
		start_t = time.time()
		self.overlay = dict()
		self.destinationDAGs = copy.deepcopy(dags)
		self.endpoints = copy.deepcopy(endpoints)
		self.routefilters = dict()
		for dst in self.pdb.getDestinations() :
			self.routefilters[dst] = []

		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()

		self.constructOverlay()		
		self.disableUnusedEdges()
		self.initializeSMTVariables()

		self.addDjikstraShortestPathConstraints()

		# Adding constraints without routeFilters
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag, False)


		print "Solving ILP without routefilters"
		solvetime = time.time()
		#modelsat = self.z3Solver.check()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime
		print "Time taken is", time.time() - solvetime

		self.routeFilterMode = False

		status = self.ilpSolver.status


		# if status == gb.GRB.INFEASIBLE :
		# 	# Model infeasible (or unbounded?). Use routefilters to solve.
		# 	self.routeFilterMode = True
		# 	self.detectDiamonds() # Detect diamonds for route-filters
		# 	#self.generateTrivialRouteFilters()
		# 	self.ilpSolver = gb.Model("C3")
		# 	self.initializeSMTVariables()

		# 	self.addDjikstraShortestPathConstraints()

		# 	# Prompted by Gurobi? 
		# 	self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 

		# 	# Adding constraints with routeFilters
		# 	for dst in dsts : 
		# 		dag = self.destinationDAGs[dst]
		# 		self.addDestinationDAGConstraints(dst, dag, True)

		# 	# # Add max-flow end point constraints


		# 	print "Solving ILP with routefilters"
		# 	solvetime = time.time()
		# 	#modelsat = self.z3Solver.check()
		# 	#self.ilpSolver.setParam(gb.GRB.Param.Method, 2)
		# 	self.ilpSolver.optimize()

		# 	status = self.ilpSolver.status
		if True: 
			if status == gb.GRB.INFEASIBLE :
				print "computing Source diamonds"
				self.routeFilterMode = True
				self.generateResilientRouteFilters()
				self.detectDiamonds()
				self.ilpSolver = gb.Model("C3")
				self.initializeSMTVariables()

				self.addDjikstraShortestPathConstraints()

				# Prompted by Gurobi? 
				# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
				# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 

				# Adding constraints with routeFilter variables at source
				for dst in dsts : 
					dag = self.destinationDAGs[dst]
					self.addDestinationDAGConstraints(dst, dag)

				# if self.t_res > 0 :
				# 	t_res = self.t_res
				# 	for endpt in self.endpoints : 
				# 		self.addResilienceConstraints(endpt[0], endpt[1], t_res)  # Add t-resilience

				solvetime = time.time()
				self.ilpSolver.optimize()
				self.z3solveTime += time.time() - solvetime

				status = self.ilpSolver.status

				# if status == gb.GRB.INFEASIBLE :
				# 	self.ilpSolver.computeIIS()
				# 	self.ilpSolver.write("model.ilp")

				# for constr in self.ilpSolver.getConstrs() :
				# 	if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				# 		print constr
				# 		self.ilpSolver.remove(constr)

				# self.ilpSolver.optimize()
				# status = self.ilpSolver.status

			#self.ilpSolver.computeIIS()
			#self.ilpSolver.write("model.ilp")
			self.z3solveTime += time.time() - solvetime
			print "Time taken is", time.time() - solvetime


		# Enable Topology Edges
		self.topology.enableAllEdges()
		# Extract Edge weights for Gurobi		
		self.getEdgeWeightModel(self.routeFilterMode)		

		#self.pdb.printPaths(self.topology)
		print "Checking for t-resilience", self.t_res
		self.pdb.validateControlPlane(self.topology, self.routefilters, self.distances, self.t_res)
		#self.topology.printWeights()
		self.printProfilingStats()

	def constructOverlay(self) :
		dsts = self.pdb.getDestinations()
		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			self.overlay[sw] = []

		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw1 in dag :
				sw2 = dag[sw1] # Edge sw1 -> sw2
				if sw2 <> None : 
					if sw2 not in self.overlay[sw1] : 
						self.overlay[sw1].append(sw2)

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
		dsts = self.pdb.getDestinations()

		constraintIndex = 0

		#print "number of destinations", len(dsts)
		for s in range(1, swCount + 1):
			if self.topology.isSwitchDisabled(s) :
				continue
			for t in range(1, swCount + 1) :
				if self.topology.isSwitchDisabled(t) :
					continue
				if s == t : 
					continue
				# if not self.topology.isConnected(s, t) :
				# 	continue # s, t is not connected in overlay, distance(s, t) does not matter

				# neighbours = self.topology.getSwitchNeighbours(s)
				# for n in neighbours :
				# 	if [s, n] not in self.routefilters[dst] :  
				# 		self.ilpSolver.addConstr(self.dist(s, t, dst) <= self.ew(s, n) + self.dist(n, t, dst))

				for sw in range(1, swCount + 1) :
					if sw == s or sw == t : continue 
					if self.topology.isSwitchDisabled(sw) : 
						continue

					self.ilpSolver.addConstr(self.dist(s, t) <= self.dist(s, sw) + self.dist(sw, t), "D-" + str(constraintIndex) + " ")	
					constraintIndex += 1


	# def addDestinationDAGConstraints(self, dst, dag) :
	# 	""" Adds constraints such that dag weights are what we want them to be """
	# 	if self.diamondsInDAG(dst): 
	# 		self.addDestinationDAGConstraintsRF(dst, dag)
	# 		return 

	# 	for sw in dag : 
	# 		nextsw = dag[sw]
	# 		while nextsw <> None :				
	# 			if nextsw == dag[sw] :
	# 				self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.ew(sw, dag[sw]))
	# 			else : 
	# 				self.ilpSolver.addConstr(self.dist(sw, nextsw) == self.dist(sw, dag[sw]) + self.dist(dag[sw], nextsw))
				
	# 			neighbours = self.topology.getSwitchNeighbours(sw)
	# 			for n in neighbours : 
	# 				if n <> dag[sw] : 
	# 					self.ilpSolver.addConstr(self.dist(sw, nextsw) <= self.ew(sw, n) + self.dist(n, nextsw) - 1)

	# 			nextsw = dag[nextsw]

	def addDestinationDAGConstraints(self, dst, dag, routeFilterMode=True) :
		""" Adds constraints such that dag weights are what we want them to be with route filtering disabled/enabled """
		
		if not routeFilterMode :
			for sw in dag : 
				t = dag[sw]
				while t <> None :				
					self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, dag[sw]) + self.dist(dag[sw], t))

					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n <> dag[sw] : 
							self.ilpSolver.addConstr(self.dist(sw, t) <= self.ew(sw, n) + self.dist(n, t) - 1)
							
					t = dag[t]
		else:
			constraintIndex = 0
			for sw in dag : 
				filterPresent = self.filterPresent(sw, dst)

				t = dag[sw]
				while t <> None :			
					# if not filterPresent : 	
					# 	self.ilpSolver.addConstr(self.dist(sw, t) == self.ew(sw, dag[sw]) + self.dist(dag[sw], t), "C-" + str(dst) + "-" + str(constraintIndex))
					# 	constraintIndex += 1
					
					
					nextsw = sw
					totalDist = 0 # Store the distance from sw to t along dag.
					while nextsw <> t : 
						totalDist += self.ew(nextsw, dag[nextsw])
						nextsw = dag[nextsw]

					self.ilpSolver.addConstr(self.dist(sw, t) <= totalDist)

					# if [sw, t] in self.endpoints : 
					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n <> dag[sw] and [sw, n] not in self.routefilters[dst] : 
							self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, t) - 1, "C-" + str(dst) + "-" + str(constraintIndex))
							constraintIndex += 1
					
					t = dag[t]			

	def addDestinationDAGConstraintsRF(self, dst, dag) :
		""" Adds constraints such that dag weights are what we want them to be with route filtering disabled/enabled """
		
		constraintIndex = 0
		for sw in dag : 
			t = dag[sw]
			while t <> None :			
				nextsw = sw
				totalDist = 0 # Store the distance from sw to t along dag.
				while nextsw <> t : 
					totalDist += self.ew(nextsw, dag[nextsw])
					nextsw = dag[nextsw]

				self.ilpSolver.addConstr(self.dist(sw, t) <= totalDist)

				if [sw, dst] in self.endpoints : 
					# Route filtering equations
					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n <> dag[sw] : 
							self.ilpSolver.addConstr(totalDist <= 100000*self.rf(sw,n,dst) + self.ew(sw, n) + self.dist(n, t) - 1, "C-" + str(dst) + "-" + str(constraintIndex))
							constraintIndex += 1
				
				t = dag[t]			


	# def addMaxFlowConstraints(self, src, dst, t_res) :
	# 	swCount = self.topology.getSwitchCount()

	# 	#self.maxFlowVars[src][dst] = self.ilpSolver.addVar(vtype=gb.GRB.CONTINUOUS, name="MaxF" + "-" + str(src)+":"+str(dst))

	# 	flowVar = defaultdict(lambda:defaultdict(lambda:None))
	# 	for sw1 in range(1, swCount + 1) :
	# 		for sw2 in self.topology.getAllSwitchNeighbours(sw1) :
	# 			flowVar[sw1][sw2] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS, name="F" + "-" + str(sw1)+":"+str(sw2))

	# 	self.ilpSolver.update()

	# 	for sw1 in range(1, swCount + 1) :
	# 		inFlow = 0
	# 		outFlow = 0
	# 		for sw2 in self.topology.getAllSwitchNeighbours(sw1) :
	# 			inFlow += flowVar[sw2][sw1]
	# 			outFlow += flowVar[sw1][sw2]

	# 		if sw1 == src : 
	# 			#self.ilpSolver.addConstr(outFlow - inFlow == self.maxFlowVars[src][dst])
	# 			self.ilpSolver.addConstr(outFlow - inFlow == t_res + 1)
	# 		elif sw1 == dst : 
	# 			self.ilpSolver.addConstr(inFlow - outFlow == t_res + 1)
	# 		else :
	# 			self.ilpSolver.addConstr(outFlow - inFlow == 0)				

	# 	# Add resilience constraint.
	# 	#self.ilpSolver.addConstr(self.maxFlowVars[src][dst] >= t_res + 1)

	# 	# Add route filter semantic constraints
	# 	for sw1 in range(1, swCount + 1) :
	# 		for sw2 in self.topology.getSwitchNeighbours(sw1) : 
	# 			self.ilpSolver.addConstr(self.rf(sw1, sw2, dst) + flowVar[sw1][sw2] <= 1)

	# def addResilienceConstraints(self, src, dst, t_res) :
	# 	""" Ensure that the route-filters at source do not reduce resilience"""
	# 	dag = self.destinationDAGs[dst]
	# 	rfs = 0
	# 	allNeighbours =  self.topology.getAllSwitchNeighbours(src)
	# 	neighbours =  self.topology.getSwitchNeighbours(src) 

	# 	if len(neighbours) == 1 : 
	# 		if len(allNeighbours) < t_res + 1 : 
	# 			print "Flow from ", src, " to ", dst, " cannot be ", t_res," resilient."
	# 		return # Resilient

	# 	t_res = t_res - (len(allNeighbours) - len(neighbours)) # Unused paths
	# 	if t_res <= 0 : 
	# 		return # Resilient

	# 	filters = []
	# 	for n in neighbours :
	# 		if n <> dag[src] :
	# 			filters.append(self.rf(src, n, dst))
		
	# 	self.leastSubsetFilters(filters, t_res) # Atleast t_res filters must be zero for t_res + 1 paths (one through dag).


	def getEdgeWeightModel(self, routeFilterMode=True) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) : 
				if n not in self.overlay[sw] :
					self.topology.addWeight(sw, n, float(100000))
					#print sw, n, 1000
				else : 
				# ew_rat = self.fwdmodel.evaluate(self.ew(sw,n))
				# self.topology.addWeight(sw, n, float(ew_rat.numerator_as_long())/float(ew_rat.denominator_as_long()))
					ew = self.ew(sw, n).x
					# if [sw,n] in self.hiddenEdges : 
					# 	ew = 1000
					self.topology.addWeight(sw, n, float(ew))

		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) :
				if s == t : continue
				self.distances[s][t] = self.dist(s,t).x
		# 		#print s,t, self.distances[s][t]

		if not routeFilterMode :
			# Route filters not used. 
			return 

		# totalRouteFilters = 0
		# setRouteFilters = 0
		# for dst in dsts : 
		# 	dag = self.destinationDAGs[dst]
		# 	#self.findRouteFilters(dst, dag)
		# 	for sw in dag : 
		# 		if sw == dst : continue
		# 		neighbours = self.overlay[sw]
		# 		for n in neighbours : 
		# 			if n <> dag[sw] : 
		# 				totalRouteFilters += 1
		# 			if [sw,dst] in self.endpoints :
		# 				rf = self.rf(sw,n,dst).x
		# 				if rf > 0 and n <> dag[sw]:
		# 					if [sw, n] not in self.routefilters[dst] :
		# 						self.routefilters[dst].append([sw,n])
		
		# for dst in dsts : 
		# 	setRouteFilters += len(self.routefilters[dst])
		# print "Ratio of routefilters : ", setRouteFilters, totalRouteFilters 

	# def findRouteFilters(self, dst, dag) :
	# 	""" Finds the required route filters for dst from model """
	
	# 	for sw in dag : 
	# 		t = dag[sw]
	# 		while t <> None :			
	# 			nextsw = sw
	# 			totalDist = 0 # Store the distance from sw to t along dag.
	# 			while nextsw <> t : 
	# 				totalDist += self.ew(nextsw, dag[nextsw]).x
	# 				nextsw = dag[nextsw]

	# 			if [sw, dst] in self.endpoints : 
	# 				# Route filtering equations
	# 				neighbours = self.overlay[sw]
	# 				for n in neighbours : 
	# 					if n <> dag[sw] : 
	# 						if n == t : 
	# 							distvar = 0
	# 						else : 
	# 							distvar = self.dist(n, t).x
	# 						if totalDist <= self.ew(sw, n).x + distvar - 1 : 
	# 							# Route filter not required
	# 							pass
	# 						else :
	# 							if [sw, n] not in self.routefilters[dst] :
	# 								self.routefilters[dst].append([sw,n])
				
	# 			t = dag[t]			

	def detectDiamonds(self, onlyDetect=False) :
		""" Detecting diamonds in the different dags. A diamond is 
		defined as a subgraph of the overlay where there are two paths from s to t
		such that the two paths belong to different destination Dags. This implies that
		there are two shortest paths from s to t which is not enforceable with route filtering """
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()
		
		if not onlyDetect : 
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
					if dag1[swDiv] == None : continue 
					# Detect a diamond
					if swDiv in dag2 : 
						if dag2[swDiv] == None : continue
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

		print self.dstDiamonds

		# Generate Route Filters
		self.generateRouteFilters()

		# # Assign ranks
		# for dst in self.dstDiamonds : 
		# 	diamondpaths = self.dstDiamonds[dst]
		# 	for dpath1 in diamondpaths : 
		# 		for dpath2 in diamondpaths : 
		# 			if dpath1 == dpath2 : continue
		# 			if len(dpath1) >= len(dpath2) : continue 
		# 			# check if dpath1 completely in dpath2
		# 			start = dpath1[0]
		# 			end = dpath1[len(dpath1) - 1]
		# 			if start in dpath2 and end in dpath2 : 
		# 				# From this and condition 2 (dpath1 < dpath2), dpath1 is strict subpath of dpath2
		# 				self.addDependency(dpath1, dpath2, dst)

		# totalRanks = 0
		# for s in range(1, swCount + 1) : 
		# 	for t in range(1, swCount + 1) : 
		# 		totalRanks += len(self.diamondPaths[s][t])

		# print "Finding ranks"
		# assignedRanks = 0
		# while assignedRanks < totalRanks :
		# 	# Find a suitable source-dst pair to assign ranks
		# 	for s in range(1, swCount + 1) : 
		# 		for t in range(1, swCount + 1) : 
		# 			if len(self.diamondPaths[s][t]) > 0 and len(self.switchRanks[s][t]) <> len(self.diamondPaths[s][t]): 
		# 				subsetOnlyEdges = []
		# 				supersetOnlyEdges = []
		# 				unConstrainedEdges = []
		# 				assignedEdges = []
		# 				diamonds = self.diamondPaths[s][t]
		# 				for dst in diamonds : 
		# 					path = diamonds[dst]
		# 					if self.isUnconstrained(path, dst) : 
		# 						unConstrainedEdges.append(path[1])
		# 					elif self.isSubsetOnly(path, dst) : 
		# 						subsetOnlyEdges.append(path[1])
		# 					elif path[1] in self.switchRanks[s][t] : 
		# 						assignedEdges.append(path[1])
		# 					elif self.isSupersetOnly(path, dst) : 
		# 						supersetOnlyEdges.append(path[1])
							
		# 				#print s,t, subsetOnlyEdges, supersetOnlyEdges, unConstrainedEdges, assignedEdges
		# 				#print diamonds, self.switchRanks[s][t], len(self.switchRanks[s][t]), len(self.diamondPaths[s][t])

		# 				if len(subsetOnlyEdges) + len(unConstrainedEdges) + len(assignedEdges) == len(diamonds) : 
		# 					# Largest Diamond. Set Ranks at will
		# 					if len(assignedEdges) > 1 : 
		# 						print "Not possible, error"
		# 						exit(0)
		# 					elif len(assignedEdges) == 1 : 
		# 						currRank = 2
		# 					else : 
		# 						currRank = 1
		# 					for n in unConstrainedEdges :
		# 						self.switchRanks[s][t][n] = currRank
		# 						currRank += 1
		# 						assignedRanks += 1
		# 					for n in subsetOnlyEdges : 
		# 						self.switchRanks[s][t][n] = currRank
		# 						if currRank == 1 : 
		# 							# Need to make sure the subset paths are set to 1
		# 							for dst in diamonds : 
		# 								path = diamonds[dst]
		# 								if path[1] == n : 
		# 									dependencies = self.getDependencies(path, dst)
		# 									for dpath in dependencies : 
		# 										if dpath[1] not in self.switchRanks[dpath[0]][dpath[len(dpath) - 1]] : 
		# 											self.switchRanks[dpath[0]][dpath[len(dpath) - 1]][dpath[1]] = 1 # Cannot be lower ranked 
		# 											assignedRanks += 1
		# 										elif dpath[1] in self.switchRanks[dpath[0]][dpath[len(dpath) - 1]] : 
		# 											if self.switchRanks[dpath[0]][dpath[len(dpath) - 1]][dpath[1]] > 1 : 
		# 												print "Violation of invariant!" 
		# 												exit(0)
		# 						if currRank > 1 : 
		# 							# Can remove dependencies of smaller paths
		# 							for dst in diamonds : 
		# 								path = diamonds[dst]
		# 								if path[1] == n : 
		# 									self.removeDependencies(path, dst)
		# 						currRank += 1
		# 						assignedRanks += 1	
		# 				if len(supersetOnlyEdges) + len(unConstrainedEdges) + len(subsetOnlyEdges) == len(diamonds) and len(supersetOnlyEdges) == 1 :
		# 					# Set the superset Edge to rank 1 (no contradtictions)
		# 					currRank = 1
		# 					for n in supersetOnlyEdges : 
		# 						self.switchRanks[s][t][n] = currRank 
		# 						assignedRanks += 1
		# 						currRank += 1
		# 						for dst in diamonds : 
		# 							path = diamonds[dst]
		# 							if path[1] == n : 
		# 								self.removeDependencies(path, dst)
		# 					for n in subsetOnlyEdges : 
		# 						self.switchRanks[s][t][n] = currRank 
		# 						assignedRanks += 1
		# 						currRank += 1
		# 						for dst in diamonds : 
		# 							path = diamonds[dst]
		# 							if path[1] == n : 
		# 								self.removeDependencies(path, dst)
		# 					for n in unConstrainedEdges :
		# 						self.switchRanks[s][t][n] = currRank
		# 						currRank += 1
		# 						assignedRanks += 1

	
	# def diamondsInDAG(self, dst) :
	# 	""" returns if there are diamonds in the dag"""
	# 	if len(self.dstDiamonds[dst]) > 0 : 
	# 		return True
	# 	else :
	# 		return False

	# def addDependency(self, path1, path2, dst) : 
	# 	""" Diamonds: path1 is a subpath of path2 in dag of dst"""
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)

	# 	s2 = path2[0]
	# 	t2 = path2[len(path2) - 1]
	# 	key2 = str(s2) + "-" + str(t2) + ":" + str(dst)

	# 	# Dependent diamond paths
	# 	self.dependencyFlag[key1] = True
	# 	self.dependencyFlag[key2] = True 
			
	# 	if key1 in self.dependencyList : 
	# 		self.dependencyList[key1].append(path2)
	# 	else : 
	# 		self.dependencyList[key1] = [path2]

	# 	if key2 in self.dependencyList : 
	# 		self.dependencyList[key2].append(path1)
	# 	else : 
	# 		self.dependencyList[key2] = [path1]

	# def getDependencies(self, path1, dst) : 
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
	# 	if key1 in self.dependencyList : 
	# 		return self.dependencyList[key1]
	# 	else : 
	# 		return []

	# def isUnconstrained(self, path1, dst) :
	# 	""" Returns if path1's rank is not dependent with any other path rank"""
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
	# 	if key1 in self.dependencyFlag :
	# 		return False
	# 	else :
	# 		return True 

	# def isSubsetOnly(self, path1, dst) :
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
	# 	if key1 not in self.dependencyList : return False
	# 	dpaths = self.dependencyList[key1]
	# 	for dpath in dpaths : 
	# 		if dpath[0] not in path1 or dpath[len(dpath) - 1] not in path1 :
	# 			return False
	# 	return True 

	# def isSupersetOnly(self, path1, dst) :
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
	# 	if key1 not in self.dependencyList : return False
	# 	dpaths = self.dependencyList[key1]
	# 	for dpath in dpaths : 
	# 		if path1[0] not in dpath or path1[len(path1) - 1] not in dpath :
	# 			return False
	# 	return True 

	# def removeDependencies(self, path1, dst) :
	# 	""" Removes dependencies of all paths subset of path as path is not sp"""
	# 	s1 = path1[0]
	# 	t1 = path1[len(path1) - 1]
	# 	key1 = str(s1) + "-" + str(t1) + ":" + str(dst)
	# 	dpaths = self.dependencyList[key1]
	# 	self.dependencyList[key1] = []
	# 	del self.dependencyFlag[key1]

	# 	for dpath in dpaths : 
	# 		s2 = dpath[0]
	# 		t2 = dpath[len(dpath) - 1]
	# 		key2 = str(s2) + "-" + str(t2) + ":" + str(dst)
	# 		dpaths2 = self.dependencyList[key2]
	# 		newdpaths2 = []
	# 		for dpath2 in dpaths2 : 
	# 			if dpath2 <> path1 :
	# 				newdpaths2.append(dpath2)
	# 		if len(newdpaths2) == 0 :
	# 			# Unconstrained 
	# 			self.dependencyList[key2] = []
	# 			del  self.dependencyFlag[key2]
	# 		else : 
	# 			self.dependencyList[key2] = newdpaths2

	# def getRank(self, s, t, nextsw) : 
	# 	""" Rank of path from s to t via nextsw (which is neighbour of s """
	# 	if nextsw in self.switchRanks[s][t] :
	# 		return self.switchRanks[s][t][nextsw]
	# 	elif len(self.switchRanks[s][t]) > 0 :
	# 		# There exists a diamond from s-t, but nextsw not in any diamond paths. Return a high rank
	# 		return 10000
	# 	else :
	# 		# No diamonds from s-t. Shortest Path
	# 		return 1

	# def isDiamondSource(self, s, dst) :
	# 	if dst not in self.dstDiamonds : 
	# 		return False
	# 	diamonds = self.dstDiamonds[dst]
	# 	for dpath in diamonds : 
	# 		if dpath[0] == s :
	# 			return True
	# 	return False

	# def isDiamondDestination(self, t) :
	# 	swCount = self.topology.getSwitchCount()
	# 	for s in range(1, swCount + 1) :
	# 		if len(self.switchRanks[s][t]) > 0 :
	# 			return True
	# 	return False

	# def isOnDiamond(self, dst, src) : 
	# 	""" Returns if path from src to dst is on a diamond """
	# 	dag = self.destinationDAGs[dst]
	# 	diamonds = self.dstDiamonds[dst]
	# 	nextsw = src
	# 	while nextsw <> None:
	# 		for dpath in diamonds : 
	# 			if nextsw in dpath : 
	# 				return True
	# 		nextsw = dag[nextsw]
	# 	return False


	# def addDiamondConstraints(self) :
	# 	swCount = self.topology.getSwitchCount()
		
	# 	for s in range(1, swCount + 1) :
	# 		for t in range(1, swCount + 1) : 
	# 			if len(self.diamondPaths[s][t]) > 0 : 
	# 				# Diamonds exist. Add constraints to ensure path weights follow ranking
	# 				diamonds = self.diamondPaths[s][t]
	# 				neighbours = self.topology.getSwitchNeighbours(s)
	# 				for dst1 in diamonds :
	# 					nextsw1= diamonds[dst1][1] # Neighbour of s
	# 					rank1 = self.switchRanks[s][t][nextsw1]
	# 					if rank1 > 1 : 
	# 						for n in neighbours : 
	# 							if n not in self.switchRanks[s][t] : 
	# 								# Higher ranked path should be strictly greater in distance
	# 								self.ilpSolver.addConstr(self.ew(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, n) + self.dist(n, t) - 1)

	# 								if [s, nextsw1] not in self.hiddenEdges : 
	# 									self.hiddenEdges.append([s, nextsw1])

	# 					# for dst2 in diamonds : 
	# 					# 	nextsw2 = diamonds[dst2][1] # Neighbour of s
	# 					# 	rank2 = self.switchRanks[s][t][nextsw2] 
	# 					# 	if rank2 > rank1 :
	# 					# 		# Higher ranked path
	# 					# 		self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, nextsw2) + self.dist(nextsw2, t) - 1)


	# 				#Constraints to ensure highest rank path is shorter than other non-ranked paths
					
	# 				# neighbours = self.topology.getSwitchNeighbours(s)
	# 				# for dst1 in diamonds :
	# 				# 	nextsw1= diamonds[dst1][1] # Neighbour of s
	# 				# 	rank1 = self.switchRanks[s][t][nextsw1]
	# 				# 	if rank1 == len(diamonds) :
	# 				# 		# Highest Rank Path
	# 				# 		for n in neighbours : 
	# 				# 			if n not in diamondNeighbours : 
	# 				# 				self.ilpSolver.addConstr(self.dist(s,nextsw1) + self.dist(nextsw1, t) <= self.dist(s, n) + self.dist(n, t) - 1)


	# def modifyDAGs(self) :
	# 	self.unmodifiedDestinationDAGs = copy.deepcopy(self.destinationDAGs)
	# 	swCount = self.topology.getSwitchCount()
	# 	self.routefilters = dict()
	# 	dsts = self.pdb.getDestinations()
	# 	self.reroutedEdges = []
	# 	self.hiddenEdges = []

	# 	print "Original DAGs"
	# 	print self.destinationDAGs


	# 	for s in range(1, swCount + 1) :
	# 		diamondDsts = []
	# 		for t in range(1, swCount + 1) : 
	# 			if len(self.diamondPaths[s][t]) > 0 : 
	# 				diamondDsts.append(t)

	# 		if len(diamondDsts) < 1 : continue # No diamonds.			
	# 		elif len(diamondDsts) >= 1 : 
	# 			# Only one diamond, can modify DAGs
	# 			for t in diamondDsts : 
	# 				diamonds = self.diamondPaths[s][t]
	# 				for dst1 in diamonds :
	# 					spath = diamonds[dst1]
	# 					nextsw1 = spath[1] # Neighbour of s
	# 					rank1 = self.switchRanks[s][t][nextsw1] 
	# 					if rank1 > 1 : 
	# 						dag1 = self.destinationDAGs[dst1]
	# 						dag1[s] = None 


	# 	self.generateRouteFilters()
					
	# # 				if rank1 == 1 : 
	# # 					for dst2 in diamonds : 
	# # 						if dst2 <> dst1 : 
	# # 							# Rank > 1. Reroute s to spath
	# # 							path2 = diamonds[dst2]
	# # 							# Rerouting
	# # 							self.reroute(dst2, path2, spath)

	# # 		else : 	
	# # 			# More than one diamond at source. 
	# # 			# If a destination DAG has to be rerouted along multiple paths
	# # 			# (It is a lower ranked path in two diamonds) 
	# # 			# => Reroute along longer path.
	# # 			rerouteDstPaths = dict()
	# # 			for t in diamondDsts : 
	# # 				diamonds =  self.diamondPaths[s][t]
	# # 				firstRankPath = self.getFirstRankPath(s,t)
	# # 				for dst1 in diamonds : 
	# # 					path1 = diamonds[dst1]
	# # 					rank1 = self.switchRanks[s][t][path1[1]]
	# # 					diamondDsts = [] # Destinations sharing diamond path <path1>
	# # 					if rank1 > 1 :
	# # 						for dst2 in dsts : 
	# # 							if path1 in self.dstDiamonds[dst2] and dst2 not in diamondDsts : 
	# # 								diamondDsts.append(dst2)

	# # 						for dst2 in diamondDsts : 
	# # 						# Higher ranked path, needs rerouting
	# # 							if dst2 not in rerouteDstPaths :
	# # 								rerouteDstPaths[dst2] = [[path1, firstRankPath]]
	# # 							else : 
	# # 								rerouteDstPaths[dst2].append([path1, firstRankPath])

	# # 			for dst1 in rerouteDstPaths : 
	# # 				if len(rerouteDstPaths[dst1]) >= 1 : 
	# # 					# Part of multiple diamonds, reroute to longest first rank path
	# # 					# Sort by path length, and reroute depending on largest diamond
	# # 					rerouteDstPaths[dst1] = sorted(rerouteDstPaths[dst1], key=lambda p: len(p[0]), reverse=True) 
	# # 					# First element of the list will have the longest diamond path for dst
	# # 					path1 = rerouteDstPaths[dst1][0][0]
	# # 					spath = rerouteDstPaths[dst1][0][1]
	# # 					self.reroute(dst1, path1, spath)

		
	# # 	print "\n\n"
	# # 	print self.destinationDAGs
	# # 	print "\n\n"

	# # 	print self.dstDiamonds
		
	# # 	for s in range(1, swCount + 1) :
	# # 		for t in range(1, swCount + 1) : 
	# # 			if len( self.switchRanks[s][t] ) > 0 : 
	# # 				print s, t, self.diamondPaths[s][t], self.switchRanks[s][t]

	# # 	print self.detectDiamonds(onlyDetect=True)

	# def reroute(self, rdst, path, spath) :
	# 	""" Reroute all dsts using path to spath """ 

	# 	dag = self.destinationDAGs[rdst]
	# 	# Start from s and send dag2 traffic through the largest
	# 	# subpath of <spath>
	# 	dag[spath[0]] = spath[1] 
	# 	for i in range(1, len(spath) - 1) : 
	# 		if spath[i] not in dag : 
	# 			dag[spath[i]] = spath[i + 1]
	# 		else :
	# 			# Switch in dag2 
	# 			break 

	# def getFirstRankPath(self, s, t) : 
	# 	diamonds = self.diamondPaths[s][t]
	# 	for dst in diamonds : 
	# 		path = diamonds[dst]
	# 		rank = self.switchRanks[s][t][path[1]]
	# 		if rank == 1 : 
	# 			return path

	def generateRouteFilters(self) :
		""" Generate the set of routefilters from diamonds"""

		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()

		# Rerouting process generates route filters for diamond paths. 
		# However, to ensure the path in the dag is followed, we need
		# to ensure it is the shortest path among the other paths.  
		for s in range(1, swCount + 1) :
			for t in range(1, swCount + 1) : 
				if len(self.diamondPaths[s][t]) > 0 : 
					diamonds = self.diamondPaths[s][t]
					for dst1 in diamonds : 
						path1 = diamonds[dst1]

						# Find other destinations sharing this path in the diamond
						filterDsts = []
						for dst in dsts : 
							if path1 in self.dstDiamonds[dst] : 
								filterDsts.append(dst)

						
						for dst in filterDsts : 
							""" Disable other diamond paths """
							for diamond in diamonds.values() :
								nextsw = diamond[1]

								# add s-nextsw to dst's route filters
								if [s, nextsw] not in self.routefilters[dst] and nextsw <> path1[1] : 
									self.routefilters[dst].append([s, nextsw])
							
							
							# dag = self.destinationDAGs[dst]
							# # Disable all edges in other diamond paths
							# for dst2 in diamonds : 
							# 	path2 = diamonds[dst2]
							# 	if path1 <> path2 : 
							# 		#print dst, path1, path2
							# 		for i in range(len(path2) - 1) :
							# 			if [path2[i], path2[i+1]] not in self.routefilters[dst] :
							# 				if path2[i] in dag and dag[path2[i]] == path2[i+1] : 
							# 					continue  
							# 				self.routefilters[dst].append([path2[i], path2[i+1]])
	

		print self.routefilters
	# 	print self.dstDiamonds

	def filterPresent(self, sw, dst) :
		""" Returns true if some filter present on switch sw for dst"""
		routefilters = self.routefilters[dst]
		for rf in routefilters : 
			if rf[0] == sw : 
				return True
		return False

	def generateTrivialRouteFilters(self) :
		""" Generates trivial route filters """
		dsts = self.pdb.getDestinations()
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw in dag : 
				for n in self.topology.getSwitchNeighbours(sw) :
					if n <> dag[sw] and [sw, n] not in self.routefilters[dst] : 
						self.routefilters[dst].append([sw,n])

	def generateResilientRouteFilters(self) :
		""" Only source routefilters will affect resilience: Edge disjointedness"""
		dsts = self.pdb.getDestinations()
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw in dag : 
				if sw == dst : continue
				if [sw, dst] not in self.endpoints : 
					for n in self.topology.getSwitchNeighbours(sw) :
						if n <> dag[sw] and [sw, n] not in self.routefilters[dst] : 
							self.routefilters[dst].append([sw,n])


	# def modifyDAGs(self) :
	# 	self.origialDestinationDAGs = copy.deepcopy(self.destinationDAGs)
		
	# 	swCount = self.topology.getSwitchCount()
	# 	dsts = self.pdb.getDestinations()

	# 	# Rerouting process generates route filters for diamond paths. 
	# 	# However, to ensure the path in the dag is followed, we need
	# 	# to ensure it is the shortest path among the other paths.  
	# 	for s in range(1, swCount + 1) :
	# 		for t in range(1, swCount + 1) : 
	# 			if len(self.diamondPaths[s][t]) > 0 : 
	# 				diamonds = self.diamondPaths[s][t]
	# 				for dst1 in diamonds : 
	# 					path1 = diamonds[dst1]

	# 					# Find other destinations sharing this path in the diamond
	# 					filterDsts = []
	# 					for dst in dsts : 
	# 						if path1 in self.dstDiamonds[dst] : 
	# 							filterDsts.append(dst)

						
	# 					for dst in filterDsts : 
	# 						""" Disable the diamond path """
	# 						dag = self.destinationDAGs[dst]
	# 						dag[s] = None 

	# def findRouteFilters(self) : 
	# 	""" Generate the rest of the route filters """ 
	# 	for pc in range(self.pdb.getPacketClassRange()) :
	# 		src = self.pdb.getSourceSwitch(pc)
	# 		dst = self.pdb.getDestinationSwitch(pc)
	# 		genesisPath = self.pdb.getPath(pc)

	# 		# Add route filters such that path from src-> dst is genesisPath
	# 		path = self.topology.getShortestPath(src, dst, self.routefilters[dst])

	# 		while genesisPath <> path:
	# 			# Find first divergence
	# 			print path, genesisPath
	# 			i = 0
	# 			while genesisPath[i] == path[i]:
	# 				i += 1

	# 			self.routefilters[dst].append([path[i - 1], path[i]])

	# 			# Update path
	# 			path = self.topology.getShortestPath(src, dst, self.routefilters[dst])
	# 			if path == [] : 
	# 				break

 
	# def analyzeDiamonds(self) : 
	# 	swCount = self.topology.getSwitchCount()
	# 	dsts = self.pdb.getDestinations()
	# 	for s in range(1, swCount + 1) :
	# 		for t in range(1, swCount + 1) : 
	# 			if len(self.diamondPaths[s][t]) > 0 : 
	# 				diamonds = self.diamondPaths[s][t]
	# 				for dst1 in diamonds : 

	def leastSubsetFilters(self, routefilters, N) :
		""" Add constraints such that the smallest N elements in the set routefilters
		are equal to 0 """
		T = len(routefilters)
		sortedFilters = []
		while len(sortedFilters) < T : 
			[maxF, routefilters] = self.bubbleMax(routefilters)
			sortedFilters.append(maxF)

		sumFilters = 0
		for i in range(N) : 
			sumFilters += sortedFilters[T - N + i]

		self.ilpSolver.addConstr(sumFilters == 0)
	

	def bubbleMax(self, filters) :
		""" Returns the smallest filter, and the rest of the filter set """

		newFilters = []
		maxX = filters.pop()
		while len(filters) <> 0 :
			x = filters.pop()
			xmax = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS)
			xmin = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS)
			absdiff = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS)
			self.ilpSolver.update()

			self.ilpSolver.addConstr(2*xmax == maxX + x + absdiff)
			self.ilpSolver.addConstr(2*xmin == maxX + x - absdiff)
			self.ilpSolver.addConstr(maxX - x <= absdiff)
			self.ilpSolver.addConstr(maxX - x >= -1 * absdiff)

			maxX = xmax
			newFilters.append(xmin)

		return [maxX, newFilters]


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