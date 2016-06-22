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
import matplotlib.pyplot as plt

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
		self.t_res = 0

		# Constants
		self.MAX_GUROBI_ITERATIONS = 100
		self.minimalFilterSolveFlag = False

		self.inconsistentRFs = 0

		# Route Filter Optimizations
		self.filterDependencies = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))

		# Endpoint resilience
		self.endpointResilience = defaultdict(lambda:defaultdict(lambda:None))


	def initializeSMTVariables(self) :
		swCount = self.topology.getSwitchCount()

		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.distVars = [[[0 for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)] 
		self.routefiltersVars = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))
		self.maxFlowVars = defaultdict(lambda:defaultdict(lambda:None))

		dsts = self.pdb.getDestinations()

		for sw1 in range(1,swCount+1):
			for sw2 in self.topology.getSwitchNeighbours(sw1) :
				self.edgeWeights[sw1][sw2] = self.ilpSolver.addVar(lb=1.00, ub=10000, vtype=gb.GRB.CONTINUOUS, name="E-" + str(sw1)+"-"+str(sw2) + "_")

		for sw1 in range(1,swCount+1):
			for sw2 in range(1, swCount + 1) :
				# dst = 0 is the default value 
				self.distVars[sw1][sw2][0] = self.ilpSolver.addVar(lb=0.00, vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2) + "_")
				# for dst in dsts : 
				# 	self.distVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00,vtype=gb.GRB.CONTINUOUS, name="D-" + str(sw1)+"-"+str(sw2)+"-"+str(dst) + " ")

		# for endpt in self.endpoints : 
		# 	for sw2 in self.topology.getSwitchNeighbours(endpt[0]) : 
		# 		self.routefiltersVars[endpt[0]][sw2][endpt[1]] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS, name="RF" + "-" + str(endpt[0])+"-"+str(sw2)+"-"+str(endpt[1])+"_")

		for dst in dsts:
			dag = self.destinationDAGs[dst]
			for sw1 in dag : 
				for sw2 in self.topology.getSwitchNeighbours(sw1) : 
					self.routefiltersVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.BINARY, name="RF" + "-" + str(sw1)+":"+str(sw2)+"-"+str(dst))
		

		self.ilpSolver.update()

	def initializeRouteFilters(self) :
		self.routefilters = dict()
		for dst in self.pdb.getDestinations() :
			self.routefilters[dst] = []

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

	def enforceDAGs(self, dags, endpoints):
		""" Enforce the input destination dags """
		start_t = time.time()
		self.overlay = dict()
		self.destinationDAGs = copy.deepcopy(dags)
		self.spGraphs = []

		# Create list of dags 
		# for dag in self.destinationDAGs.values() : 
		# 	# print dag
		# 	spGraph = dict()
		# 	for sw in dag :
		# 		spGraph[sw] = []
		# 		if dag[sw] <> None : 
		# 			spGraph[sw].append(dag[sw])

		# 	self.spGraphs.append(spGraph)

		self.endpoints = copy.deepcopy(endpoints)
		
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinations()

		self.constructOverlay()	
		#self.overlayConnectivity()	
		self.disableUnusedEdges()
		self.initializeSMTVariables()
		self.initializeEndpointResilience()

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
	
		self.routeFilterMode = False
		status = self.ilpSolver.status

		if status == gb.GRB.INFEASIBLE :
			if self.minimalFilterSolveFlag : 
				self.minimalFilterSolve()
			else : 
				print "solving ILP with routefilters"
				self.routeFilterMode = True
				self.initializeRouteFilters()
				self.detectDiamonds()
				diamondLoss = self.calculateResilienceLoss()

				#self.findValidCycles()
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

				if status == gb.GRB.INFEASIBLE :
					# Perform inconsistency analysis using Gurobi
					attempts = 1
					inconsistencyVal = self.findInconsistency()
					while inconsistencyVal:
						inconsistencyVal = self.findInconsistency()
						attempts += 1
						if attempts > self.MAX_GUROBI_ITERATIONS :
							break
					print "inconsistency attempts", attempts
					print "diamond loss", diamondLoss

			print "Time taken is", time.time() - solvetime


		# Enable Topology Edges
		self.topology.enableAllEdges()
		# Extract Edge weights for Gurobi		
		self.getEdgeWeightModel(self.routeFilterMode)		

		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.routefilters, self.t_res)
		#self.topology.printWeights()
		self.printProfilingStats()


	"""
	An IIS is a subset of the constraints and variable bounds of the original model. 
	If all constraints in the model except those in the IIS are removed, the model is still infeasible. 
	However, further removing any one member of the IIS produces a feasible result.
	"""
	def findInconsistency(self) :
		""" Find inconsistent set of equations """
		self.ilpSolver = gb.Model("C3")
		self.initializeSMTVariables()
		dsts = self.pdb.getDestinations()

		# Prompted by Gurobi? 
		# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
		# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 

		self.addDjikstraShortestPathConstraints()
		# Adding constraints with routeFilter variables at source
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag)

		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime

		status = self.ilpSolver.status
		if status == gb.GRB.INFEASIBLE :
			solvetime = time.time()
			self.ilpSolver.computeIIS()
			self.z3solveTime += time.time() - solvetime

			#self.plotUnsatCore()
			# Pick filters greedily?
			self.maximizeResilienceRouteFilter()
			return True
		else :
			print "Consistent!!!"
			# swCount = self.topology.getSwitchCount()
			# for i in range(1, swCount + 1) :
			# 	for j in range(1, swCount + 1) :
			# 		for k in range(1, swCount + 1) :
			# 			if k in self.filterDependencies[i][j] :
			# 				print i,j,k, self.filterDependencies[i][j][k]
			# 				if k in self.routefilters :
			# 					print [i,j] in self.routefilters[k]
			return False

	def greedyRouteFilter(self) :
		""" Pick route filters based on greedy counts """
		maxRF = [0,0,0,0]
		
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "RF" :
					# Route filter constraint
					if int(fields[4]) in self.filterDependencies[int(fields[1])][int(fields[2])] : 
						self.filterDependencies[int(fields[1])][int(fields[2])][int(fields[4])] += 1
					else :
						self.filterDependencies[int(fields[1])][int(fields[2])][int(fields[4])] = 1

					dependencies = self.filterDependencies[int(fields[1])][int(fields[2])][int(fields[4])]
					if dependencies >= maxRF[3] :
						maxRF = [int(fields[1]), int(fields[2]), int(fields[4]), dependencies]
		

		self.addRouteFilter(maxRF[0], maxRF[1], maxRF[2])

	def maximizeResilienceRouteFilter(self) :
		""" Pick route filters based on maximizing filters """
		

		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "RF" :
					# Route filter constraint
					if [int(fields[1]), int(fields[4])] not in self.endpoints : 
						# Not a source filter. Does not affect resilience. Pick this.
						self.addRouteFilter(int(fields[1]), int(fields[2]), int(fields[4]))
						return

		# All filters are source filters. Choose source with most resilience
		mostResilientRF = [0,0,0,100000]
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "RF" :
					totalres = len(self.topology.getAllSwitchNeighbours(int(fields[1])))
					res = self.endpointResilience[int(fields[1])][int(fields[4])]
					if totalres - res < mostResilientRF[3] :
						mostResilientRF = [int(fields[1]), int(fields[2]), int(fields[4]), totalres - res]
		
		self.addRouteFilter(mostResilientRF[0], mostResilientRF[1], mostResilientRF[2])

	def calculateResilienceLoss(self) :
		""" Calculate loss of resilience due to route filtering """
		loss = 0

		for endpt in self.endpoints : 
			totalres = len(self.topology.getAllSwitchNeighbours(endpt[0]))
			loss += totalres - self.endpointResilience[endpt[0]][endpt[1]] 

		print "Loss of resilience :", loss
		return loss

	def plotUnsatCore(self) :
		graph = nx.DiGraph()
		edges = []
		colors = []
		dottedEdges = []
		dottedColors = []
		for constr in self.ilpSolver.getConstrs() :
			
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "RF" :
					# RF, s, sw', t, dst 
					dst = int(fields[4])
					dag = self.destinationDAGs[dst]
					s = int(fields[1])
					graph.add_node(s)
					t = int(fields[3])
					graph.add_node(t)

					# find a color based on dst
					color = dst * 45 % 256
					sw = s
					while sw <> t:
						graph.add_node(sw)
						graph.add_edge(sw, dag[sw])
						# Assign color to edges
						if (sw, dag[sw]) not in edges : 
							edges.append((sw, dag[sw]))
							colors.append(color)
						else : 
							ind = edges.index((sw, dag[sw]))
							colors[ind] = color

						sw = dag[sw]						
					
					graph.add_node(int(fields[2]))
					graph.add_edge(s, int(fields[2])) # s -> sw'
					# Assign color to dottedEdges
					if (s, int(fields[2])) not in dottedEdges : 
						dottedEdges.append((s, int(fields[2])))
						dottedColors.append(color)
					else: 
						ind = dottedEdges.index((s, int(fields[2])))
						dottedColors[ind] = color

					graph.add_edge(int(fields[2]), t) # sw' -> t
					# Assign color to dottedEdges
					if (int(fields[2]), t) not in dottedEdges : 
						dottedEdges.append((int(fields[2]), t))
						dottedColors.append(color)
					else : 
						ind = dottedEdges.index((int(fields[2]), t))
						dottedColors[ind] = color


		pos = nx.spring_layout(graph)
		# switch labels
		switchLabels = dict()
		for sw in graph.nodes() :
			switchLabels[sw] = str(sw)

		nx.draw_networkx_nodes(graph, pos, cmap=plt.get_cmap('jet'), node_color = 'g')
		nx.draw_networkx_edges(graph, pos, edgelist=dottedEdges, edge_color=dottedColors, style="dashed", arrows=True)
		nx.draw_networkx_edges(graph, pos, edgelist=edges, edge_color=colors, arrows=True)
		nx.draw_networkx_labels(graph,pos,switchLabels)
		#nx.draw_networkx_edges(G, pos, edgelist=black_edges, arrows=False)
		plt.show()

	def minimalFilterSolve(self) :
		""" Find inconsistent set of equations """
		self.ilpSolver = gb.Model("C3")
		self.initializeSMTVariables()
		dsts = self.pdb.getDestinations()

		# Prompted by Gurobi? 
		# self.ilpSolver.setParam(gb.GRB.Param.BarHomogeneous, 1) 
		# self.ilpSolver.setParam(gb.GRB.Param.Method, 2) 

		self.addDjikstraShortestPathConstraints()
		# Adding constraints with routeFilter variables at source
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraintsRF(dst, dag)

		self.addMinimalFilterObjective()
		solvetime = time.time()
		self.ilpSolver.optimize()
		self.z3solveTime += time.time() - solvetime


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

				for sw in self.topology.getSwitchNeighbours(s) :
					self.ilpSolver.addConstr(self.dist(s, t) <= self.ew(s, sw) + self.dist(sw, t), "D-" + str(constraintIndex) + " ")	
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
				t = dag[sw]
				while t <> None :							
					nextsw = sw
					totalDist = 0 # Store the distance from sw to t along dag.
					while nextsw <> t : 
						totalDist += self.ew(nextsw, dag[nextsw])
						nextsw = dag[nextsw]

					self.ilpSolver.addConstr(self.dist(sw, t) <= totalDist)
 
					neighbours = self.topology.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n <> dag[sw] and [sw, n] not in self.routefilters[dst] : 
							self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, t) - 1, "RF-" + str(sw) + "-" 
								+ str(n) + "-" + str(t) + "-" + str(dst) + "-" + str(constraintIndex))
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

				# Route filtering equations
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n <> dag[sw] : 
						self.ilpSolver.addConstr(totalDist <= 100000*self.rf(sw,n,dst) + self.ew(sw, n) + self.dist(n, t) - 1, "C-" + str(dst) + "-" + str(constraintIndex))
						constraintIndex += 1
				
				t = dag[t]			

	def addMinimalFilterObjective(self) : 
		totalRouteFilters = 0
		dsts = self.pdb.getDestinations()
		for dst in dsts:
			dag = self.destinationDAGs[dst]
			for sw1 in dag : 
				for sw2 in self.topology.getSwitchNeighbours(sw1) : 
					if sw2 == dag[sw1] : continue
					else : totalRouteFilters += self.rf(sw1,sw2,dst)

		self.ilpSolver.setObjective(totalRouteFilters, gb.GRB.MINIMIZE)

	def addRouteFilter(self, sw1, sw2, dst) :
		""" Add rf at sw1 -> sw2 for dst """
		if [sw1, sw2] not in self.routefilters[dst] :
			self.routefilters[dst].append([sw1, sw2]) 
			self.inconsistentRFs += 1

			# Update resilience if source filter.
			if [sw1, dst] in self.endpoints : 
				self.endpointResilience[sw1][dst] -= 1

		print "RF",sw1, sw2, dst

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

		totalRouteFilters = 0
		setRouteFilters = 0
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw in dag : 
				if sw == dst : continue
				neighbours = self.overlay[sw]
				for n in neighbours : 
					if n <> dag[sw] : 
						totalRouteFilters += 1
					# if [sw,dst] in self.endpoints :
					# 	rf = self.rf(sw,n,dst).x
					# 	if rf > 0 and n <> dag[sw]:
					# 		if [sw, n] not in self.routefilters[dst] :
					# 			self.routefilters[dst].append([sw,n])
		
		for dst in dsts : 
			setRouteFilters += len(self.routefilters[dst])
		print "Ratio of routefilters : ", setRouteFilters, totalRouteFilters 
		self.calculateResilienceLoss()

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
							
						#print s,t, subsetOnlyEdges, supersetOnlyEdges, unConstrainedEdges, assignedEdges
						#print diamonds, self.switchRanks[s][t], len(self.switchRanks[s][t]), len(self.diamondPaths[s][t])

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

		# Generate Route Filters
		self.generateRouteFilters()
	
	def diamondsInDAG(self, dst) :
		""" returns if there are diamonds in the dag"""
		if len(self.dstDiamonds[dst]) > 0 : 
			return True
		else :
			return False

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

	def getSwitchRank(self, s, t, nextsw) : 
		""" Rank of path from s to t via nextsw (which is neighbour of s """
		if nextsw in self.switchRanks[s][t] :
			return self.switchRanks[s][t][nextsw]
		elif len(self.switchRanks[s][t]) > 0 :
			# There exists a diamond from s-t, but nextsw not in any diamond paths. Return a high rank
			return 10000
		else :
			# No diamonds from s-t. Shortest Path
			return 1

	def isDiamondSource(self, s, dst) :
		if dst not in self.dstDiamonds : 
			return False
		diamonds = self.dstDiamonds[dst]
		for dpath in diamonds : 
			if dpath[0] == s :
				return True
		return False

	def isDiamondDestination(self, t) :
		swCount = self.topology.getSwitchCount()
		for s in range(1, swCount + 1) :
			if len(self.switchRanks[s][t]) > 0 :
				return True
		return False

	def isOnDiamond(self, dst, src) : 
		""" Returns if path from src to dst is on a diamond """
		dag = self.destinationDAGs[dst]
		diamonds = self.dstDiamonds[dst]
		nextsw = src
		while nextsw <> None:
			for dpath in diamonds : 
				if nextsw in dpath : 
					return True
			nextsw = dag[nextsw]
		return False

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

						nextsw1= path1[1] # Neighbour of s
						rank1 = self.getSwitchRank(s,t,nextsw1)
						
						for dst in filterDsts : 
							""" Disable other diamond paths """
							for diamond in diamonds.values() :
								nextsw2 = diamond[1]
								rank2 = self.getSwitchRank(s,t,nextsw2)

								if rank2 < rank1 : 
									# add s-nextsw2 to dst's route filters
									self.addRouteFilter(s, nextsw2, dst)
	

		# print self.routefilters
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

	def createDestinationSPGraphs(self, t) :
		""" Find all shortest paths ending in t """

		spGraph = dict()
		spGraph[t] = [] # No neighbours for dst
		
		dsts = self.pdb.getDestinations()
		for dst in dsts :
			dstGraph = dict()
			dstGraph[t] = []
			dag = self.destinationDAGs[dst]

			while True:
				changeFlag = False
				for sw in dag :
					if dag[sw] in spGraph and sw not in spGraph: 
						spGraph[sw] = [dag[sw]]
						changeFlag = True
				if not changeFlag :
					# All paths added to spGraph.
					break

			# combine dstGraph with spGraph
			for sw in dstGraph :
				if sw in spGraph :
					for n in dstGraph[sw] :
						if n not in spGraph[sw] :
							spGraph[sw].append(n)
				else :
					spGraph[sw] = dstGraph[sw]

		# Check if target is still empty
		if spGraph[t] <> [] :
			print "Some error!"

		return spGraph

	def findValidCycles(self) :
		""" Find valid cycles"""

		self.totalCycles = 0
		swCount = self.topology.getSwitchCount()
		dstSPGraphs = []

		# Create destination SPGraphs
		for sw in range(1, swCount + 1) :
			dstSPGraphs.append(self.createDestinationSPGraphs(sw))

		for i in range(len(dstSPGraphs)) :
			sp1 = dstSPGraphs[i] 
			# Something with route filters!
			if len(sp1) <= 1 : 
				continue

			# Initialize disabled Edges to the requisite route filters
			disabledEdges = [] 
			dsts = self.pdb.getDestinations()
			for dst in dsts :
				dag = self.destinationDAGs[dst]
				filters = self.routefilters[dst]
				for rf in filters :
					if rf[0] in sp1 and dag[rf[0]] in sp1[rf[0]] :
						# path corresponding to filter is in sp1
						disabledEdges.append(rf)
			
			for j in range(i + 1, len(dstSPGraphs)):
				sp2 = dstSPGraphs[j]
				self.findCycle(sp1, sp2, disabledEdges)
				#print "Edges disabled are", disabledEdges

		print "Total edges disabled are", self.totalCycles

	def findCycle(self, sp1, sp2, disabledEdges) :
		""" sp1 forward, sp2 backward """ 
		#print "finding cycles between", sp1, sp2
		dsts = self.pdb.getDestinations()
		graph = nx.DiGraph()
		for sw in sp1 : 
			graph.add_node(sw)

		for sw in sp2 : 
			graph.add_node(sw)

		for sw in sp1 : 
			for n in sp1[sw] : 
				graph.add_edge(sw, n)

		for sw in sp2 :
			for n in sp2[sw] :
				if sw in sp1 and n in sp1[sw] : 
					continue
				elif [sw, n] in disabledEdges : 
					continue
				else :
					# Add backward edge to graph 
					graph.add_edge(n, sw)

		# Graph constructed. For every node in sp1, 
		# find and break cycles till all are removed.
		while True : 
			try :
				cycle = nx.find_cycle(graph, orientation='original')
			except :
				cycle = []
			if cycle == [] :
				break
			isValidCycle = True
			if not self.checkCycleValidity(cycle) :
				# not valid cycle. Do not add route filter.
				isValidCycle = False
			#print "CYCLE ======== ", cycle, cycle[0], len(cycle) 
			# find edge to disable
			prevEdge = cycle[0]
			if prevEdge[0] in sp1 and prevEdge[1] in sp1[prevEdge[0]] :	
				inSp1 = True 
			else :
				inSp1 = False
			edgeRemoved = False
			for i in range(1, len(cycle)) :
				edge = cycle[i]
				if edge[0] in sp1 and edge[1] in sp1[edge[0]] and not inSp1 : 
					# backward edge in sp2 entering sp1. Can disable this for route-filtering.
					disabledEdges.append([prevEdge[1], prevEdge[0]]) # disable the forward edge while creating the directed combined graph
					graph.remove_edge(prevEdge[0], prevEdge[1]) # Remove backward edge from graph
					#print "Removing edge", prevEdge[0], prevEdge[1]
					edgeRemoved = True
					if not isValidCycle : 
						# do not add route filter
						break

					self.totalCycles += 1
					# Find route-filter corresponding to this edge disable
					filterDsts = []
					for dst in dsts :
						# trace cycle and find largest overlap with cycle and DAG. 
						dag = self.destinationDAGs[dst]
						if edge[0] in dag and edge[1] == dag[edge[0]] :
							sw = edge[1]
							count = 1
							while sw <> None :
								if (sw, dag[sw]) in cycle : 
									count += 1
								else :
									break
								sw = dag[sw]
							filterDsts.append([dst, count])

					filterDsts = sorted(filterDsts, key=lambda p: p[1], reverse=True)
					maxOverlap = filterDsts[0][1] 
					for fdst in filterDsts :
						if fdst[1] == maxOverlap :
							# Add route filter
							self.addRouteFilter(prevEdge[1], prevEdge[0], fdst[0])
					break

				prevEdge = [edge[0], edge[1]]
				if edge[0] in sp1 and edge[1] in sp1[edge[0]] :
					inSp1 = True
					#print edge, "True"
				else :
					#print edge, "False"
					inSp1 = False
				#print "Edge removed status", edgeRemoved

			if not edgeRemoved : 
				# No transition from sp2 to sp1 seen. 
				# Cycle[0] in sp1, last edge will be disabled
				if cycle[0][0] in sp1 and cycle[0][1] in sp1[cycle[0][0]] :
					disabledEdges.append([prevEdge[1], prevEdge[0]]) # disable the forward edge while creating the directed combined graph
					graph.remove_edge(prevEdge[0], prevEdge[1]) # Remove backward edge from graph
					#print "Removing edge", prevEdge[0], prevEdge[1]
					self.totalCycles += 1
					if isValidCycle : 
						# do  add route filter	
						filterDsts = []
						for dst in dsts :
							# trace cycle and find largest overlap with cycle and DAG. 
							dag = self.destinationDAGs[dst]
							if cycle[0][0] in dag and cycle[0][1] == dag[cycle[0][0]] :
								sw = cycle[0][1]
								count = 1
								while sw <> None :
									if (sw, dag[sw]) in cycle : 
										count += 1
									else :
										break
									sw = dag[sw]
								filterDsts.append([dst, count])

						filterDsts = sorted(filterDsts, key=lambda p: p[1], reverse=True)
						maxOverlap = filterDsts[0][1] 
						for fdst in filterDsts :
							if fdst[1] == maxOverlap :
								# Add route filter
								self.addRouteFilter(prevEdge[1], prevEdge[0], fdst[0])
				else :
					print "Problemo"
					exit(0)

	def checkCycleValidity(self, cycle) :
		""" Check if cycle indeed is valid (and not filtered) """
		dsts = self.pdb.getDestinations()
		for i in range(len(cycle)) : 
			edge = cycle[i]
			for dst in dsts : 
				dag = self.destinationDAGs[dst]
				filters = self.routefilters[dst]
				for rf in filters :
					if rf == [edge[0], edge[1]] : 
						# Check if previous edge belongs to dst dag
						prevEdge = cycle[(i - 1 + len(cycle)) % len(cycle)]
						if prevEdge[0] in dag and prevEdge[1] == dag[prevEdge[0]] :
							# do not consider cycle
							return False

		return True




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