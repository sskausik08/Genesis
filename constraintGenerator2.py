from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
import time
import random
import metis
import networkx as nx

class ConstraintGenerator2(object) :
	def __init__(self, topo, policyCount=20, fuzzy=True) :
		self.topology = topo

		# Network Forwarding Function
		self.F = Function('F', IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())
		self.N = Function('N', IntSort(), IntSort(), BoolSort())
		self.pc = Int('pc') # Generic variable for packet classes

		self.z3Solver = Solver()
		self.z3Solver.set(unsat_core=True)
		self.fwdmodel = None 

		self.count = policyCount
		# Policy Database. 
		self.pdb = PolicyDatabase()

		# Topology Optimizations 
		self.fatTreeOptimizeFlag = False
		
		# Fuzzy Synthesis Constants. 
		self.CUT_THRESHOLD = 1000
		self.GRAPH_SIZE_THRESHOLD = 1

		# Fuzzy Synthesis Flags 
		self.fuzzySynthesisFlag = fuzzy


		# Profiling Information.
		self.z3addTime = 0  # Time taken to add the constraints.
		self.z3solveTime = 0 # Time taken to solve the constraints. 
		self.metisTime = 0	# Time taken to partition  the graphs.
		self.z3SolveCount = 0	# Count of z3 solve instances. 


		start_t = time.time()
		print "Adding Constraints at " + str(start_t)

		# Generate the assertions.
		self.addPolicies()
		assert self.pdb.relationalClassCreationFlag == True

		# Add Unreachable Constraints 
		self.addUnreachableHopConstraints()
	
		if self.fuzzySynthesisFlag : 
			rcGraphs = self.pdb.getRelationalClassGraphs()

			for rcGraph in rcGraphs :
				(rcGraphSat, synPaths) = self.enforceGraphPoliciesFuzzy(rcGraph)
				for pc in synPaths.keys() :
					self.pdb.addPath(pc, synPaths[pc])

			self.enforceMulticastPolicies()		
		else :
			self.enforceUnicastPolicies()
			self.enforceMulticastPolicies()		

		self.pdb.printPaths()

		end_t = time.time()
		#print self.pdb.getPath(1)
		
		# for pc in range(self.pdb.getPacketClassRange()) :
		# 	print "pc#" + str(pc) + ":" + str(self.pdb.validateIsolationPolicy(pc))
		print "Time taken to solve the " + str(policyCount) + " policies with fuzzy flag " + str(fuzzy) + "is " + str(end_t - start_t)

	def addPolicies(self) :
		# self.addReachabilityPolicy("0", 1, "0", 5, [17,6])
		# self.addReachabilityPolicy("1", 1, "1", 2)
		# self.addReachabilityPolicy("2", 3, "2", 6)
		# self.addReachabilityPolicy("3", 3, "3", 6)
		# self.addTrafficIsolationPolicy(["0", "0"] , ["1", "1"])
		# self.addTrafficIsolationPolicy(["1", "1"] , ["2", "2"])

		# self.addEqualMulticastPolicy("9", 1, ["9", "9"], [6, 5])
		# self.addMulticastPolicy("8", 1, ["8", "8"], [6, 5, 4])
		# self.addReachabilityPolicy("4", 1, "4", 2)
		# self.addReachabilityPolicy("5", 1, "5", 2)
		# self.addReachabilityPolicy("6", 1, "6", 2)
		# self.addTrafficIsolationPolicy(["5", "5"] , ["4", "4"])
		# self.addTrafficIsolationPolicy(["4", "4"] , ["3", "3"])
		# self.addTrafficIsolationPolicy( ["2", "2"], ["5", "5"])


		for i in range(self.count) :
			self.addReachabilityPolicy(str(i), 1, str(i), 5)

		for i in range(self.count, self.count * 2) :
			self.addReachabilityPolicy(str(i), 5, str(i), 1, [12])

		for i in range(self.count - 1) :
			self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+1), str(i+1)])

		for i in range(self.count - 2) :
			self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+2), str(i+2)])

		self.addReachabilityPolicy(str(100), 15, str(100), 16)
		self.addTrafficIsolationPolicy([str(100), str(100)] , [str(0), str(0)])
		self.addTrafficIsolationPolicy([str(100), str(100)] , [str(10), str(10)])
		self.addTrafficIsolationPolicy([str(100), str(100)] , [str(1), str(1)])
		self.addTrafficIsolationPolicy([str(100), str(100)] , [str(11), str(11)])

		# for i in range(self.count - 3) :
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+3), str(i+3)])
		
		# for i in range(self.count - 4) :
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+4), str(i+4)])

		# for i in range(self.count - 10):
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+7), str(i+7)])
		
		self.pdb.createRelationalClasses()

	def addReachabilityPolicy(self, srcIP, s, dstIP, d, W=None) :
		""" s = next hop switch of source host(s) 
			d = next hop switch of destination host(s)
			W = Waypoint Set (list of nodes) """

		# Add policy to PDB : 
		pc = self.pdb.addAllowPolicy(srcIP, s, dstIP, d, W)

	def addTrafficIsolationPolicy(self, ep1, ep2) : 
		# Isolation of traffic for packet classes (end-points) ep1 and ep2. 
		pc = self.pdb.addIsolationPolicy(ep1,ep2) # Returns [pc1,pc2]

	def addEqualMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		pc = self.pdb.addEqualMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	def addMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		pc = self.pdb.addMulticastPolicy(srcIP, srcSw, dstIPs, dstSws)

	def enforceUnicastPolicies(self) :
		# Add Topology Constraints 
		self.addTopologyConstraints(0, self.pdb.getPacketClassRange())

		""" Enforcement of Policies stored in the PDB. """
		# Create Relational Packet Classses.
		relClasses = self.pdb.createRelationalClasses()

		for relClass in relClasses :
			# Independent Synthesis of relClass.
			self.z3Solver.push()
			for pc in relClass :
				if not self.pdb.isMulticast(pc) :  
					policy = self.pdb.getAllowPolicy(pc)
					self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1]) 

			# Add traffic constraints. 
			for pno in range(self.pdb.getIsolationPolicyCount()) :
				pc = self.pdb.getIsolationPolicy(pno)
				pc1 = pc[0]
				pc2 = pc[1]
				if pc1 in relClass and pc2 in relClass : 
					self.addTrafficIsolationConstraints(pc1, pc2)


			# Each relational class can be synthesised independently.
			modelsat = self.z3Solver.check()
			if modelsat == z3.sat : 
				print "SAT"
				self.fwdmodel = self.z3Solver.model()
				for pc in relClass :
					self.pdb.addPath(pc, self.getPathFromModel(pc))
					
			else :
				print "Input Policies not realisable"

			self.z3Solver.pop()

	def enforceGraphPolicies(self, rcGraph, pathConstraints=None) :
		""" Synthesis of the Relational Class Graph given some path constraints"""

		# Clean up path Constraints.
		if not pathConstraints == None :
			pathConstraints = self.cleanPathConstraints(pathConstraints)

		synPaths = dict()

		self.z3Solver.push()
		pclist = []
		for node in rcGraph.nodes() :
			pclist.append(int(node))

		if len(pclist) == 0 :
			print "Function should not be called on empty graph."
			exit(0)

		for pc in pclist : 
			if not self.pdb.isMulticast(pc) :  
				policy = self.pdb.getAllowPolicy(pc)
				self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1]) 

				# Add Topology Constraints
				self.addTopologyConstraints(pc)

		# Add traffic constraints. 
		for pno in range(self.pdb.getIsolationPolicyCount()) :
			pc = self.pdb.getIsolationPolicy(pno)
			pc1 = pc[0]
			pc2 = pc[1]
			if pc1 in pclist and pc2 in pclist : 
				self.addTrafficIsolationConstraints(pc1, pc2)

		if not pathConstraints == None :
			# path Constraint : [pc1, path]. All pcs which are connected to this rcGraph across the cut
			# will be added as Path constraints. 
			for pathConstraint in pathConstraints : 
				for pno in range(self.pdb.getIsolationPolicyCount()) :
					pc = self.pdb.getIsolationPolicy(pno)
					pc1 = pc[0]
					pc2 = pc[1]
					if pc1 in pclist and pc2 == pathConstraint[0] :
						self.addPathIsolationConstraints(pc1, pathConstraint[1], pathConstraint[0])
					elif pc2 in pclist and pc1 == pathConstraint[0] :
						self.addPathIsolationConstraints(pc2, pathConstraint[1], pathConstraint[0])


		# Each relational class is be synthesised independently.
		print "Starting Z3 check for " + str(pclist)
		modelsat = self.z3Solver.check()
		if modelsat == z3.sat : 
			graphSat = True
			print "SAT"
			self.fwdmodel = self.z3Solver.model()
			for pc in pclist :
				synPaths[pc] = self.getPathFromModel(pc)
				self.pdb.addPath(pc, self.getPathFromModel(pc))		
		else :
			graphSat = False
			print "Input Policies not realisable"
			print pclist
			print pathConstraints
			print self.z3Solver.unsat_core()
			exit(0)

		self.z3Solver.pop()
		return (graphSat, synPaths)

			
	def enforceGraphPoliciesFuzzy(self, rcGraph, pathConstraints=None) :
		""" Fuzzy Enforcement of Policies in arg 'rcGraph' """

		# Clean up path Constraints.
		if not pathConstraints == None :
			pathConstraints = self.cleanPathConstraints(pathConstraints)
		
		synPaths = dict()

		# If the graph size is smaller than a threshold, perform complete synthesis. 
		if rcGraph.number_of_nodes() <= self.GRAPH_SIZE_THRESHOLD :
			(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,pathConstraints)
			return (graphSat, synPaths)

		# Fuzzy Synthesis of rcGraph.
		print "Metis starting. Is this the problem?"
		start_t = time.time()
		(edgecuts, partitions) = metis.part_graph(rcGraph, 2) # Note : Metis overhead is minimal.
		end_t = time.time() - start_t
		print str(end_t) + " is the metis partition time."

		# If the min-cut between the two partitions is greater than a threshold, dont partition. 
		if edgecuts > self.CUT_THRESHOLD :
			(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,pathConstraints)
			return (graphSat, synPaths)

		# Graph Partitioned in two. Apply Fuzzy Synthesis on both of them. 
		# Append the first graph as constraints to second. 

		# Create the Graphs.
		rcGraph1 = nx.Graph()
		rcGraph2 = nx.Graph()

		rc1empty = True
		rc2empty = True
		i = 0
		for node in rcGraph.nodes():
			pc = int(node)
			if partitions[i] == 0 :
				rcGraph1.add_node(int(rcGraph.node[pc]['switch']), switch=str(rcGraph.node[pc]['switch'])) 
				rc1empty = False
			elif partitions[i] == 1 :
				rcGraph2.add_node(int(rcGraph.node[pc]['switch']), switch=str(rcGraph.node[pc]['switch'])) 
				rc2empty = False
			i += 1

		if rc1empty == True or rc2empty == True: 
			print "Cannot be partitioned"
			# Cannot partition the graph further. Apply synthesis. 
			(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,pathConstraints)
			return (graphSat, synPaths)

		cutEdges = [] # Paths from one graph must be passed as path constraints to other graph.
		for edge in rcGraph.edges() :
			if edge[0] in rcGraph1.nodes() and edge[1] in rcGraph1.nodes() :
				# Internal edge. Add to rcGraph1.
				rcGraph1.add_edge(*edge)
			elif edge[0] in rcGraph2.nodes() and edge[1] in rcGraph2.nodes() :
				# Internal edge. Add to rcGraph1.
				rcGraph2.add_edge(*edge)
			else :
				# Cut Edges. 
				cutEdges.append(edge)

		if pathConstraints == None : 
			(rcGraph1Sat, synPaths1) = self.enforceGraphPoliciesFuzzy(rcGraph1)
		else :
			(rcGraph1Sat, synPaths1) = self.enforceGraphPoliciesFuzzy(rcGraph1, pathConstraints)

		if rcGraph1Sat == False : 
			# Function cannot find a solution on the complete graph, as partial graph failed.
			return (False, [])

		if pathConstraints == None :
			localPathConstraints = []
		else :
			localPathConstraints = list(pathConstraints)

		for cut in cutEdges :
			if cut[0] in rcGraph1 : 
				localPathConstraints.append([cut[0], synPaths1[cut[0]]])	
			elif cut[1] in rcGraph1 : 
				localPathConstraints.append([cut[1], synPaths1[cut[1]]])

		if localPathConstraints == [] :
			(rcGraph2Sat, synPaths2) = self.enforceGraphPoliciesFuzzy(rcGraph2)
		else :
			(rcGraph2Sat, synPaths2) = self.enforceGraphPoliciesFuzzy(rcGraph2, localPathConstraints)

		if rcGraph2Sat == True : 
			# Partial graph solutions can be combined. 
			synPaths1.update(synPaths2)
			return (True, synPaths1)
		else : 
			# Recovery can be performed at this level, as additional constraints failed the solution.
			pass
	
	def cleanPathConstraints(self, pathConstraints) :
		newPathConstraints = []
		for pathConstraint in pathConstraints :
			exists = False
			for newPathConstraint in newPathConstraints :
				if newPathConstraint[0] == pathConstraint[0] :
					exists = True
					break
			if exists :
				continue
			else :
				newPathConstraints.append(pathConstraint)

		return newPathConstraints

	def enforceMulticastPolicies(self) :
		# Enforcement of Mutltcast Policies. 
		for pc in range(self.pdb.getPacketClassRange()) :
			if self.pdb.isMulticast(pc) :
				self.z3Solver.push()
			
				policy = self.pdb.getMulticastPolicy(pc)

				if self.pdb.isEqualMulticast(pc) : 
					self.addEqualMulticastConstraints(policy[1], policy[3], pc, 8) 
				else :
					self.addEqualMulticastConstraints(policy[1], policy[3], pc)

				modelsat = self.z3Solver.check()
				if modelsat == z3.sat : 
					print "SAT"
					self.fwdmodel = self.z3Solver.model()	
					paths = self.getMulticastPathFromModel(pc)
					""" IMPORTANT NOTE : So, the Multicast Policy enforcement provides the paths asked, but also 
					other paths not needed (Because of non-restriction of paths). So, the model provides paths for 
					all dst in the destination list, but also other destinations not needed. Instead of refining the 
					constraints, Genesis will store only paths asked by the policy. 
					Caveat : This works, because our Multicast functionality is treated in isolation. If we need to 
					isolate Multicast flows, then the problme could get a lot trickier. """
					dstPaths = []
					for path in paths : 
						for dst in policy[3] :
							if dst in path : 
								dstPaths.append(path)
								break

					self.pdb.addPath(pc, dstPaths)		
				else :
					print "Multicast Input Policy" +  str(policy) + " is not realisable"
					self.pdb.addPath(pc, [])	

				self.z3Solver.pop()

	def addUnreachableHopConstraints(self) :
		swCount = self.topology.getSwitchCount()
		for sw in range(1,swCount+1) :
			# \forall n such that n \notin neighbours or n \not\eq sw . F(sw,n,pc,1) = False
			# Cannot reach nodes which are not neighbours in step 1. 
			# This constraint is needed because there is no restriction from the above constraints 
			# regarding the values of non-neighbours.
			neighbours = self.topology.getSwitchNeighbours(sw)
			for s in range(1,swCount + 1) :
				if s == sw or s in neighbours : 
					continue
				else :
					self.z3Solver.add(ForAll(self.pc, self.F(sw,s,self.pc,1) == False))


	def addTopologyConstraints(self, pcStart, pcEnd=0) :
		if pcEnd == 0 :
			""" Topology Constraint for one packet class"""
			pcEnd = pcStart + 1

		swCount = self.topology.getSwitchCount()
		# \forall sw \forall n \in neighbours(sw) and NextHop = {n | F(sw,n,pc,1) = True}. |NextHop| \leq 1 
		# None or only one of F(sw,n,pc,1) can be true.
		for sw in range(1,swCount+1) :
			for pc in range(pcStart, pcEnd) :
				if not self.pdb.isMulticast(pc) : 
					""" Unicast packet class """
					neighbours = self.topology.getSwitchNeighbours(sw)

					# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
					topoAssert = False
					unreachedAssert = True

					for n in neighbours : 
						neighbourAssert = self.F(sw,n,pc,1) == True
						unreachedAssert = And(unreachedAssert, self.F(sw,n,pc,1) == False)
						for n1 in neighbours :
							if n == n1 : 
								continue
							else :
								neighbourAssert = And(neighbourAssert, self.F(sw,n1,pc,1) == False)
						topoAssert = Or(topoAssert, neighbourAssert)

					topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
					self.z3Solver.add(topoAssert)
				else :
					""" Multicast packet class. No restrictions on forwarding set """
					pass	
			

	def addNeighbourConstraints(self) :
		swCount = self.topology.getSwitchCount()
		for sw in range(0,swCount) :
			neighbours = self.topology.getSwitchNeighbours(sw)

			for i in range(swCount+1) : 
				if i in neighbours : 
					self.z3Solver.add(self.N(sw,i) == True)
				else :
					self.z3Solver.add(self.N(sw,i) == False)

	def addReachabilityConstraints(self, srcIP, srcSw, dstIP, dstSw, pc, W=None, pathlen=0) :
		if pathlen == 0 :
			# Default argument. Set to max.
			pathlen = self.topology.getMaxPathLength()

		# Specific case for a fat tree to apply path length upper bounds. 
		if self.fatTreeOptimizeFlag :
			pathlen = self.fatTreePathLengthOptimizations(W)
		

		# Add Reachability in atmost pathlen steps constraint. 
		reachAssert = self.F(srcSw,dstSw,pc,pathlen) == True
		self.z3Solver.add(reachAssert)

		# At Destination, forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(dstSw)
		
		destAssert = True
		for n in neighbours :
			destAssert = And(destAssert, self.F(dstSw,n,pc,1) == False)

		self.z3Solver.add(destAssert)

		if not W == None : 
			# Add the Waypoint Constraints. 
			for w in W :
				reachAssert = self.F(srcSw,w,pc,pathlen) == True
				self.z3Solver.add(reachAssert)

		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addPathConstraints(srcSw,pc)		
		
	def fatTreePathLengthOptimizations(self, W) :
		""" In a fat tree, source and destination are connected to edge switches. 
		Assumes all Waypoints are edge switches and provides a upper bound on max length of the path. """
		IsolationDetour = 4 # To switch from a core switch to another. 
		minPathLength = IsolationDetour + 4 # Shortest path from one-edge switch to another.  

		if W == None : 
			return minPathLength
		else : 
			if minPathLength + len(W) * 4 > self.topology.getMaxPathLength() :
				return self.topology.getMaxPathLength() 
			else :
				return minPathLength + len(W) * 4

	def addPathConstraints(self, s, pc) :
		l = Int('l')
		self.z3Solver.add(l > 0)
		self.z3Solver.add(l < self.topology.getMaxPathLength() + 1)

		neighbours = self.topology.getSwitchNeighbours(s)
		# Add assertions to ensure f(s,*) leads to a valid neighbour. 
		neighbourAssert = False
		for n in neighbours :
			neighbourAssert = Or(neighbourAssert, self.F(s,n,pc,1) == True)

		self.z3Solver.add(neighbourAssert)

		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()


		for i in range(1,swCount+1) :
			if i == s : 
				continue

			for pathlen in range(2,maxPathLen+1) :	
				reachedAssert = (Implies (self.F(s,i,pc,pathlen-1), self.F(s,i,pc,pathlen)))
				self.z3Solver.add(reachedAssert)

			ineighbours = self.topology.getSwitchNeighbours(i) 

			neighbourAssert = False

			for isw in ineighbours : 
				for pathlen in range(1,maxPathLen) :
					nextHopAssert = Implies(And(self.F(s,i,pc,pathlen) == True,self.F(i,isw,pc,1)) == True,self.F(s,isw,pc,pathlen+1) == True)
					self.z3Solver.add(nextHopAssert)

				unreachedAssert = Implies(self.F(s,i,pc,maxPathLen) == False, self.F(i,isw,pc,1) == False)
				self.z3Solver.add(unreachedAssert)	

			
			# Paths of length 2.
			path2Assert = True
			for pathlen in range(2,maxPathLen+1) :
				beforeHopAssert = False
				for isw in ineighbours : 
					beforeHopAssert = Or(beforeHopAssert, And(self.F(isw, i, pc, 1) == True, self.F(s, isw, pc, pathlen - 1) == True))
				
				path2Assert = And(path2Assert, Implies(self.F(s,i,pc,pathlen), beforeHopAssert))

			path1Assert = self.F(s,i,pc,1) == True
			self.z3Solver.add(Or(path1Assert, path2Assert))

			# Path len > 1 always.
			self.z3Solver.add(self.F(s,i,pc,0) == False)



	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """

		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.F(sw,n,pc1,1) == True, self.F(sw,n,pc2,1) == True))
				self.z3Solver.add(isolateAssert)	

	def addPathIsolationConstraints(self, pc, path, tracker=0) :
		""" Adding constraints such that the path of pc is isolated by 'path' argument"""
		i = 0
		for i in range(len(path) - 1) :
			self.z3Solver.assert_and_track(self.F(path[i], path[i+1], pc, 1) == False, "p"+str(tracker))


	def addEqualMulticastConstraints(self, srcSw, dstSwList, pc, pathlen=0) :
		if pathlen == 0 :
			# Default argument. Do normal Multicast.
			pathlen = self.topology.getMaxPathLength()
			for dstSw in dstSwList : 
				reachAssert = self.F(srcSw,dstSw,pc,pathlen) == True
				self.z3Solver.add(reachAssert)
		else :
			# Add Reachability in "exactly" pathlen steps constraint. 
			for dstSw in dstSwList : 
				reachAssert = self.F(srcSw,dstSw,pc,pathlen) == True
				reachAssert = And(reachAssert, self.F(srcSw,dstSw,pc,pathlen - 1) == False)
				self.z3Solver.add(reachAssert)

		# At Destination, forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		for dstSw in dstSwList : 
			neighbours = self.topology.getSwitchNeighbours(dstSw)
		
			destAssert = True
			for n in neighbours :
				destAssert = And(destAssert, self.F(dstSw,n,pc,1) == False)

			self.z3Solver.add(destAssert)

		# We need to ensure only a single path to destination. 
		for dst in range(1,self.topology.getSwitchCount() +1) :
			if dst == srcSw : 
				continue
			else : 
				neighbours = self.topology.getSwitchNeighbours(dst)

				# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
				singlePathAssert = False
				unreachedAssert = True

				for n in neighbours : 
					neighbourAssert = self.F(n,dst,pc,1) == True
					unreachedAssert = And(unreachedAssert, self.F(n,dst,pc,1) == False)
					for n1 in neighbours :
						if n == n1 : 
							continue
						else :
							neighbourAssert = And(neighbourAssert, self.F(n1,dst,pc,1) == False)
					singlePathAssert = Or(singlePathAssert, neighbourAssert)

				self.z3Solver.add(Or(unreachedAssert, singlePathAssert))

		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addPathConstraints(srcSw,pc)	

		# Need to add cycle constraints as well!	
		fname = "rank" + str(pc)
		rankfn = Function(fname, IntSort(), IntSort())

		self.z3Solver.add(rankfn(srcSw) == 0)
		
		for i in range(1,self.topology.getSwitchCount() +1) :
			ineighbours = self.topology.getSwitchNeighbours(i) 

			for n in ineighbours :
				self.z3Solver.add(Implies(self.F(i,n,pc,1) == True, rankfn(n) > rankfn(i)))


	def addBoundConstraints(self, pcRange) :
		self.z3Solver.add(self.pc < pcRange + 1)

	
	def getPathFromModel(self, pc) :
		def getPathHelper(s, pc) :
			path = [s]
			swCount = self.topology.getSwitchCount()
			
			for sw in range(1, swCount + 1) :
				if sw == s : 
					continue
				if is_true(self.fwdmodel.evaluate(self.F(s,sw,pc,1))) :
					path.extend(getPathHelper(sw,pc))
					return path
			
			return path

		return getPathHelper(self.pdb.getSourceSwitch(pc), pc)

	def getMulticastPathFromModel(self, pc) :
		def getPathHelper(s, pc) :
			paths = []
			swCount = self.topology.getSwitchCount()
			
			isDst = True
			for sw in range(1, swCount + 1) :
				if sw == s : 
					continue
				if is_true(self.fwdmodel.evaluate(self.F(s,sw,pc,1))) :
					isDst = False
					nextPaths = getPathHelper(sw,pc)
					for path in nextPaths :
						srcpath = [s]
						srcpath.extend(path)
						paths.append(srcpath)
			
			if isDst : 
				return [[s]]
			else : 
				return paths

		return getPathHelper(self.pdb.getSourceSwitch(pc), pc)



t = Topology()
for i in range(1,2) :
	c = ConstraintGenerator2(t, i*10, True)


# nuZ3
# maxSAT
# US Backbone, RocketFuelS