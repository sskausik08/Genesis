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

		# Route Filter Optimizations
		self.filterDependencies = defaultdict(lambda:defaultdict(lambda:defaultdict(lambda:None)))

		# Endpoint resilience
		self.endpointResilience = defaultdict(lambda:defaultdict(lambda:None))
		self.resilienceLoss = 0


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

		# for endpt in self.endpoints : 
		# 	for sw2 in self.topology.getSwitchNeighbours(endpt[0]) : 
		# 		self.routefiltersVars[endpt[0]][sw2][endpt[1]] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS, name="RF" + "-" + str(endpt[0])+"-"+str(sw2)+"-"+str(endpt[1])+"_")

		for dst in dsts:
			dag = self.destinationDAGs[dst]
			for sw1 in dag : 
				for sw2 in self.topology.getSwitchNeighbours(sw1) : 
					self.routefiltersVars[sw1][sw2][dst] = self.ilpSolver.addVar(lb=0.00, ub=1.00, vtype=gb.GRB.CONTINUOUS, name="RF" + "-" + str(sw1)+":"+str(sw2)+"-"+str(dst))
		

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

	def enforceDAGs(self, dags, endpoints, bgpExtensions=None):
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
		self.initializeEndpointResilience()
		self.initializeStaticRoutes()

		start_t = time.time()
		self.addDjikstraShortestPathConstraints()

		# Adding constraints without routeFilters
		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			self.addDestinationDAGConstraints(dst, dag, False)


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
					#print "inconsistency attempts", attempts
					#print "diamond loss", diamondLoss

			
		# self.f.write(str(len(endpoints)) + "," + str(time.time() - start_t)+"\n")
		# Enable Topology Edges
		self.topology.enableAllEdges()
		# Extract Edge weights for Gurobi		
		self.getEdgeWeightModel(self.routeFilterMode)	

		# self.f.close()	
		#self.pdb.printPaths(self.topology)
		self.pdb.validateControlPlane(self.topology, self.staticRoutes)

		#self.topology.printWeights()
		#self.printProfilingStats()
		#self.printRouteFilterDistribution()
		
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
		self.zepFile.write("Time" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(time.time() - start_t))
		self.zepFile.write("\n")
		self.zepFile.write("Static Routes" + "\t" + str(self.pdb.getPacketClassRange()) + "\t" + str(srCount) + "\t")
		self.zepFile.write("\n")
		return self.staticRouteNames

	"""
	An IIS is a subset of the constraints and variable bounds of the original model. 
	If all constraints in the model except those in the IIS are removed, the model is still infeasible. 
	However, further removing any one member of the IIS produces a feasible result.
	"""
	def findInconsistency(self) :
		""" Find inconsistent set of equations """
		self.ilpSolver = gb.Model("C3")
		self.ilpSolver.setParam('OutputFlag', 0)
		self.initializeSMTVariables()
		dsts = self.pdb.getDestinationSubnets()

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
			#self.greedyRouteFilter()
			self.minimizeStaticRoutes()
			return True
		else :
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
		

		# Find cycles for RF
		#start_t = time.time()
		#print "Number of cycles", self.findValidCycleCountFilter(maxRF)
		#print "time to find cycles is", time.time() - start_t
		self.addRouteFilter(maxRF[0], maxRF[1], maxRF[2])

	def greedyCycleFilter(self) :
		maxRF = [0,0,0,0]
		
		for constr in self.ilpSolver.getConstrs() :
			if constr.getAttr(gb.GRB.Attr.IISConstr) > 0 :
				name = constr.getAttr(gb.GRB.Attr.ConstrName) 
				fields = name.split("-")
				if fields[0] == "RF" :
					rf = [int(fields[1]), int(fields[2]), int(fields[4])]
					cycles = self.findValidCycleCountFilter(rf)
					print rf, cycles
					if cycles > maxRF[3] :
						maxRF = [rf[0], rf[1], rf[2], cycles]

		self.addRouteFilter(maxRF[0], maxRF[1], maxRF[2])

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

		sr = None
		count = 0
		for ind in range(len(staticRoutes)) : 
			if staticRoutes[ind][1] > count : 
				sr = staticRoutes[ind][0]
				count = staticRoutes[ind][1]

		# Pick the best static Route
		self.addStaticRoute(sr[0], sr[1], sr[2])

	def findResilienceLoss(self, rf, dst) :
		# Check if rf on mincut to dst
		pcs = self.pdb.getDestinationSubnetPacketClasses(dst)
		totalEdgeDisjointPaths = 0

		for pc in pcs : 
			srcSw = self.pdb.getSourceSwitch(pc)
			dstSw = self.pdb.getDestinationSwitch(pc)

			mincut = self.findMinCut(srcSw, dstSw, self.routefilters[dst])
			totalEdgeDisjointPaths += mincut

		rfs = copy.deepcopy(self.routefilters[dst])
		rfs.append(rf)

		newtotalEdgeDisjointPaths = 0

		for pc in pcs : 
			srcSw = self.pdb.getSourceSwitch(pc)
			dstSw = self.pdb.getDestinationSwitch(pc)

			mincut = self.findMinCut(srcSw, dstSw, rfs)
			newtotalEdgeDisjointPaths += mincut

		return totalEdgeDisjointPaths - newtotalEdgeDisjointPaths # Loss of resilience. Positive or 0.


	def findMinCut(self, srcSw, dstSw, routefilters) :
		# finds the minimum cut from srcSw to dstSw with disabled filters 
		rfs = copy.deepcopy(routefilters)

		visited = dict()
		bfstree = dict()
		queue1 = [srcSw]

		while len(queue1) != 0:
			sw = queue1.pop(0)
			visited[sw] = True
			if sw == dstSw : 
				# Found shortest path from srcSw to dstSw. Remove and check. 
				sw1 = dstSw 
				while sw1 != srcSw:
					edge = [bfstree[sw1], sw1]
					rfs.append(edge)
					sw1 = bfstree[sw1]

				return 1 + self.findMinCut(srcSw, dstSw, rfs)
			else :
				neighbours = self.topology.getAllSwitchNeighbours(sw)
				for n in neighbours :
					if [sw,n] in rfs : continue # Filtered. Dont explore.
					elif n in visited : continue # Switch already visited
					else : 
						if n not in queue1 : 
							queue1.append(n)
							bfstree[n] = sw

		return 0

	def findTotalResilienceLoss(self) :
		""" Calculate loss of resilience due to route filtering """
		totalresilienceLoss = 0
		self.worstResilienceLoss = 0

		for pc in range(self.pdb.getPacketClassRange()) : 
			srcSw = self.pdb.getSourceSwitch(pc)
			dstSw = self.pdb.getDestinationSwitch(pc)
			subnet = self.pdb.getDestinationSubnet(pc)

			bestMincut = self.findMinCut(srcSw, dstSw, [])
			mincut = self.findMinCut(srcSw, dstSw, self.routefilters[subnet])

			totalresilienceLoss += bestMincut - mincut
			self.worstResilienceLoss += bestMincut - 1

		return totalresilienceLoss

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
					while sw != t:
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
		self.ilpSolver.setParam('OutputFlag', 0)
		self.initializeSMTVariables()
		dsts = self.pdb.getDestinationSubnets()

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
		dsts = self.pdb.getDestinationSubnets()
		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			self.overlay[sw] = []

		for dst in dsts : 
			dag = self.destinationDAGs[dst]
			for sw1 in dag :
				sw2 = dag[sw1] # Edge sw1 -> sw2
				if sw2 != None : 
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
					self.ilpSolver.addConstr(self.dist(s, t) <= self.ew(s, sw) + self.dist(sw, t), "D-" + str(self.constraintIndex) + " ")	
					self.constraintIndex += 1


	def addDestinationDAGConstraints(self, dst, dag, routeFilterMode=True) :
		""" Adds constraints such that dag weights are what we want them to be with route filtering disabled/enabled """	
		for sw in dag :
			if dag[sw] == None :
				dstSw = sw

		if not routeFilterMode :
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
					for n in neighbours : 
						if n != dag[sw]: 
							self.ilpSolver.addConstr(totalDist <= self.ew(sw, n) + self.dist(n, dstSw) - 1, "SR-" + str(sw) + "-" 
								+ str(dag[sw]) + "-" + str(dstSw) + "-" + str(dst) + "-" + str(self.constraintIndex))
							self.constraintIndex += 1

		self.addBGPExtensionConstraints(dst, dag, routeFilterMode)		

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


	def getEdgeWeightModel(self, routeFilterMode=True) : 
		self.topology.initializeWeights()
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()
		# self.distances = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

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