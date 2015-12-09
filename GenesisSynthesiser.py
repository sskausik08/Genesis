from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx


class GenesisSynthesiser(object) :
	def __init__(self, topo, policyCount=20, Optimistic=True, TopoSlicing=True) :
		self.topology = topo

		# Network Forwarding Function
		self.Fwd = Function('Fwd', IntSort(), IntSort(), IntSort(), BoolSort())
		self.Reach = Function('Reach', IntSort(), IntSort(), IntSort(), BoolSort())

		self.R = Function('R', IntSort(), IntSort(), IntSort())
		self.L = Function('L', IntSort(), IntSort(), IntSort(), IntSort())
		self.pc = Int('pc') # Generic variable for packet classes
		
		self.z3Solver = Solver()
		self.z3Solver.set(unsat_core=True)
		self.fwdmodel = None 

		self.count = policyCount
		# Policy Database. 
		self.pdb = PolicyDatabase()

		# Topology Optimizations 
		self.fatTreeOptimizeFlag = False
		
		# Optimistic Synthesis Variables
		self.OptimisticPaths = dict()  # Stores the solutions obtained during the Optimistic synthesis procedure. 
		self.OptimisticLinkCapacityConstraints = []
		
		# Store the different retry attempts for link capacity recovery to ensure we dont repeat solutions.
		self.OptimisticLinkRecoveryAttempts = dict() 
		self.OptimisticTrackedPaths = dict()
		self.OptimisticUnsatLinkCores = []

		# Optimistic Synthesis Constants. 
		self.CUT_THRESHOLD = 10
		self.BASE_GRAPH_SIZE_THRESHOLD = 10
		self.CURR_GRAPH_SIZE_THRESHOLD = 3

		# Different Solution Recovery Variables. 
		self.DIFF_SOL_RETRY_COUNT = 4
		self.ResetOldSolutionsFlag = False

		# Link Capacity Recovery Variables
		self.LINK_RECOVERY_COUNT = 4

		# Optimistic Synthesis Flags 
		self.OptimisticSynthesisFlag = Optimistic
		self.recoveryFlag = False
		self.topologySlicingFlag = TopoSlicing
		self.synthesisSuccessFlag = True

		# SAT Encoding Flags
		self.UseQuantifiersflag = True
		self.UseTopoSAT = True
		self.addGlobalTopoFlag = False

		# Profiling Information.
		self.z3addTime = 0  # Time taken to add the constraints.
		self.z3solveTime = 0 # Time taken to solve the constraints. 
		self.metisTime = 0	# Time taken to partition  the graphs.
		self.z3SolveCount = 0	# Count of z3 solve instances. 


	def enforcePolicies(self): 
		start_t = time.time()

		# Generate the assertions.
		self.pdb.createRelationalClasses()
		assert self.pdb.relationalClassCreationFlag == True

		# Add Unreachable Constraints 
		st = time.time()
		self.addUnreachableHopConstraints() # Takes 2 seconds for a 78-node fat tree topology. 
		#tprint "Unreachable Hop Constraints take ", time.time() - st

		st = time.time()
		if(not self.OptimisticSynthesisFlag) or self.addGlobalTopoFlag :
			self.addTopologyConstraints(0, self.pdb.getPacketClassRange())
		#tprint "Time to add global topology constraints", time.time() - st
	
		if self.OptimisticSynthesisFlag : 
			rcGraphs = self.pdb.getRelationalClassGraphs()

			# Add link capacity constraints
			self.OptimisticLinkCapacityConstraints = self.pdb.getLinkCapacityConstraints()

			for rcGraph in rcGraphs :
				rcGraphSat = False
				self.CURR_GRAPH_SIZE_THRESHOLD = self.BASE_GRAPH_SIZE_THRESHOLD # reset the graph size to base value.
				
				while rcGraphSat == False and self.CURR_GRAPH_SIZE_THRESHOLD < self.topology.getSwitchCount() : 
					(rcGraphSat, synPaths) = self.enforceGraphPoliciesOptimistic(rcGraph)
					if rcGraphSat == False : 
						# Incremental Graph recovery
						self.CURR_GRAPH_SIZE_THRESHOLD = self.CURR_GRAPH_SIZE_THRESHOLD * 2 # Doubling the current graph size
						print "Incrementing the solver graph size to " + str(self.CURR_GRAPH_SIZE_THRESHOLD)

				if rcGraphSat == False :
					# Apply non-Optimistic synthesis. 
					self.enforceUnicastPolicies()

				self.synthesisSuccessFlag = self.synthesisSuccessFlag & rcGraphSat
			self.enforceMulticastPolicies()		
		else : 
			self.synthesisSuccessFlag = self.enforceUnicastPolicies()
			self.enforceMulticastPolicies()		


		if self.synthesisSuccessFlag and self.OptimisticSynthesisFlag: 
			for pc in self.OptimisticPaths : 
				self.pdb.addPath(pc, self.OptimisticPaths[pc])
			self.pdb.validatePolicies()
			self.pdb.printPaths(self.topology)
		else :
			self.pdb.validatePolicies()
			self.pdb.printPaths(self.topology)

		end_t = time.time()
		print "Time taken to solve the policies with Optimistic flag is " + str(end_t - start_t)

	def addPolicies(self) :
		self.count = 100
		pc = dict()
		for i in range(self.count) :
			pred = EqualNP("ip.src", "10.1.3.4")	
			pc[i] = self.addReachabilityPolicy(pred, "s1", "s5")


		for i in range(self.count - 6) :
			self.addTrafficIsolationPolicy(pc[i], pc[i+1])

		for i in range(self.count - 15) :
			self.addTrafficIsolationPolicy(pc[i], pc[i+2])

		# self.addReachabilityPolicy(str(100), 15, str(100), 16)
		# self.addTrafficIsolationPolicy([str(100), str(100)] , [str(0), str(0)])
		# self.addTrafficIsolationPolicy([str(100), str(100)] , [str(10), str(10)])
		# self.addTrafficIsolationPolicy([str(100), str(100)] , [str(1), str(1)])
		# self.addTrafficIsolationPolicy([str(100), str(100)] , [str(11), str(11)])

		# for i in range(self.count - 3) :
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+3), str(i+3)])
		
		# for i in range(self.count - 4) :
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+4), str(i+4)])

		# for i in range(self.count - 10):
		# 	self.addTrafficIsolationPolicy([str(i), str(i)] , [str(i+7), str(i+7)])
		

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
			for w in waypoints :
				W.append(self.topology.getSwID(w))

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

		# Create Relational Packet Classses.
		relClasses = self.pdb.createRelationalClasses()

		# switchTableConstraints = self.pdb.getSwitchTableConstraints()
		# self.addSwitchTableConstraints(switchTableConstraints)  # Adding switch table constraints.

		linkCapacityConstraints = self.pdb.getLinkCapacityConstraints()
		self.addLinkConstraints(range(self.pdb.getPacketClassRange()), linkCapacityConstraints)

		if len(linkCapacityConstraints) > 0 :
			# Cannot synthesise relational Classes independently. 
			for pc in range(self.pdb.getPacketClassRange()) :
				if not self.pdb.isMulticast(pc) : 
					policy = self.pdb.getReachabilityPolicy(pc)
					self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

			# Add traffic constraints. 
			for pno in range(self.pdb.getIsolationPolicyCount()) :
				pcs = self.pdb.getIsolationPolicy(pno)
				pc1 = pcs[0]
				pc2 = pcs[1]
				self.addTrafficIsolationConstraints(pc1, pc2)
			
			# Apply synthesis
			modelsat = self.z3Solver.check()
			if modelsat == z3.sat : 
				print "Solver return SAT"
				self.fwdmodel = self.z3Solver.model()
				for pc in range(self.pdb.getPacketClassRange()) :
					self.pdb.addPath(pc, self.getPathFromModel(pc))		
			else :
				print "Input Policies not realisable"
		else : 			
			for relClass in relClasses :
				# Independent Synthesis of relClass.
				self.z3Solver.push()
				for pc in relClass :
					if not self.pdb.isMulticast(pc) :  
						policy = self.pdb.getReachabilityPolicy(pc)
						self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

				# Add traffic constraints. 
				for pno in range(self.pdb.getIsolationPolicyCount()) :
					pc = self.pdb.getIsolationPolicy(pno)
					pc1 = pc[0]
					pc2 = pc[1]
					if pc1 in relClass and pc2 in relClass : 
						self.addTrafficIsolationConstraints(pc1, pc2)
			
				# Each relational class can be synthesised independently.
				st = time.time()
				modelsat = self.z3Solver.check()
				#tprint "Time taken to solve constraints is " + str(time.time() - st)
				if modelsat == z3.sat : 
					print "Solver return SAT"
					self.fwdmodel = self.z3Solver.model()
					for pc in relClass :
						self.pdb.addPath(pc, self.getPathFromModel(pc))
						
				else :
					print "Input Policies not realisable"
					unsatCores = self.z3Solver.unsat_core()
					for unsatCore in unsatCores :
						print str(unsatCore)


				self.z3Solver.pop()

	def enforceGraphPolicies(self, rcGraph, differentPathConstraints=None, recovery=True) :
		""" Synthesis of the Relational Class Graph given some path constraints (isolation and inequality). 
		If True, return the sat core paths for the RC Graph. 
		If False, return the unsat core paths to aid search for different constraints of isolation"""

		synPaths = dict()
		unsatLinks = []

		self.z3Solver.push()

		st = time.time()
		#tprint "Adding constraints."
		pclist = []
		for node in rcGraph.nodes() :
			pclist.append(int(node))

		if len(pclist) == 0 :
			print "Function should not be called on empty graph."
			#exit(0)

		for pc in pclist : 
			if not self.pdb.isMulticast(pc) :  
				policy = self.pdb.getReachabilityPolicy(pc)
				st = time.time()
				self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 
				#tprint "Time taken to add Reachability constraints is " + str(time.time() - st)
				
				if not self.addGlobalTopoFlag : 
					st = time.time()
					# Add Topology Constraints
					self.addTopologyConstraints(pc)
					#tprint "Time taken to add Topology constraints is " + str(time.time() - st)

		# Add traffic constraints. 
		for pno in range(self.pdb.getIsolationPolicyCount()) :
			pcs = self.pdb.getIsolationPolicy(pno)
			pc1 = pcs[0]
			pc2 = pcs[1]
			if pc1 in pclist and pc2 in pclist : 
				self.addTrafficIsolationConstraints(pc1, pc2)
			elif pc1 in pclist and pc2 in self.OptimisticPaths :
				self.addPathIsolationConstraints(pc1, self.OptimisticPaths[pc2], pc2)
			elif pc2 in pclist and pc1 in self.OptimisticPaths :
				self.addPathIsolationConstraints(pc2, self.OptimisticPaths[pc1], pc1)

		if not differentPathConstraints == None : 
			# Unsat Cores: [pc1, path]. pc1 must find a solution which is not equal to path. 
			for unsatCores in differentPathConstraints : 
				self.addDifferentSolutionConstraint(unsatCores)
				
		# Add link capacity constraints. 
		self.addLinkConstraints(pclist, self.OptimisticLinkCapacityConstraints)

		print "Starting Z3 check for " + str(pclist)
		st = time.time()
		modelsat = self.z3Solver.check()
		if modelsat == z3.sat : 
			#tprint "Time taken to solve the constraints is " + str(time.time() - st)
			rcGraphSat = True
			print "SAT"
			self.fwdmodel = self.z3Solver.model()
			for pc in pclist :
				path = self.getPathFromModel(pc)
				synPaths[pc] = path
				self.pdb.addPath(pc, path)		
				self.OptimisticPaths[pc] = path

				# Update Optimistic link capacity constraints.
				for constraint in self.OptimisticLinkCapacityConstraints : 
					try:
						index = path.index(constraint[0])
						if index == len(path) - 1:
							continue # Last element. 
						if path[index + 1] == constraint[1] :
							# Link is used. Update constraint.
							constraint[2] = constraint[2] - 1
						
						# Add pc to tracked Paths. 
						key = str(constraint[0]) + "-" + str(constraint[1])
						if key in self.OptimisticTrackedPaths : 
							self.OptimisticTrackedPaths[key].append(pc)
						else : 
							self.OptimisticTrackedPaths[key] = [pc]

					except ValueError:
						continue

		else :
			rcGraphSat = False
			print "Input Policies not realisable"
			print pclist
			unsatCores = self.z3Solver.unsat_core()
			if len(unsatCores) == 0:
				# print "Unsatisfiability not due to any partial isolation solutions to the rcGraph. Thus, solution does not exist"
				#exit(0)
				pass
			else :
				for core in unsatCores :
					fields = str(core).split("-")
					if len(fields) == 1: 
						# Path Isolation core. 
						ipc = int(fields[0])
						synPaths[ipc] = self.OptimisticPaths[ipc]
					else :
						# Link constraint core.
						print str(core) + " is the link overloaded."
						unsatLinks.append([int(fields[0]), int(fields[1])])
				# Setting the unsat Links for the recovery function. Doing this so as to not return this(like a register)
				self.OptimisticUnsatLinkCores = unsatLinks
		
		self.z3Solver.pop()

		if recovery and len(unsatLinks) > 0: 
			# Perform link capacity recovery
			rcGraphSat = self.linkcapacityRecovery(self.LINK_RECOVERY_COUNT, unsatLinks, rcGraph, differentPathConstraints)	
			if rcGraphSat == True : 
				# Send updated synPaths.
				print "Link Capacity Recovery successful"
				synPaths = dict()
				for pc in pclist : 
					synPaths[pc] = self.OptimisticPaths[pc]
		return (rcGraphSat, synPaths)
	
	def enforceGraphPoliciesOptimistic(self, rcGraph, differentPathConstraints=None) :
		""" Optimistic Enforcement of Policies in arg 'rcGraph' """

		synPaths = dict()

		# If the graph size is smaller than a threshold, perform complete synthesis. 
		if rcGraph.number_of_nodes() <= self.CURR_GRAPH_SIZE_THRESHOLD :
			if(self.topologySlicingFlag) : 
				(graphSat, synPaths) = self.applyTopologySlicing(rcGraph, differentPathConstraints)
			else :
				(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,differentPathConstraints)
			return (graphSat, synPaths)

		# Optimistic Synthesis of rcGraph.
		(edgecuts, partitions) = metis.part_graph(graph=rcGraph, nparts=2, contig=True) # Note : Metis overhead is minimal.

		# If the min-cut between the two partitions is greater than a threshold, dont partition. 
		no_attempts = 10

		random.seed(time.time())
		while edgecuts > self.CUT_THRESHOLD and no_attempts > 0:
			# try to partition into 4 and combining them with a random seed.
			print "Attempting repartitions"
			(edgecuts, partitions) = metis.part_graph(graph=rcGraph, nparts=4, contig=True) # Note : Metis overhead is minimal.

			# Combine partitions and check if edgecut is less than threshold.
			ind = 0
			for ind in range(len(partitions)) :
				if partitions[ind] == 1 and no_attempts % 2 == 0: partitions[ind] = 0
				if partitions[ind] > 1 and no_attempts % 2 == 0: partitions[ind] = 1

				if partitions[ind] % 2 == 0 and no_attempts % 2 == 1: partitions[ind] = 0
				if partitions[ind] % 2 == 1 and no_attempts % 2 == 1: partitions[ind] = 1
				ind += 1

			ind = 0
			# Recompute edgecuts.
			pclist1 = []
			pclist2 = []
			for node in rcGraph.nodes():
				pc = int(node)
				if partitions[ind] == 1 : 
					# Partition 1. 
					pclist1.append(pc)
				if partitions[ind] == 2 : 
					# Partition 2. 
					pclist2.append(pc)

			edgecuts = 0
			for pc1 in pclist1 : 
				ipcs = self.pdb.getIsolatedPolicies(pc1)
				for ipc in ipcs :
					if ipc in pclist2 :
						# cut-edge.
						edgecuts += 1	

			no_attempts -= 1

		if no_attempts < 1 and edgecuts > self.CUT_THRESHOLD: 
			# Could not find a min-edge cut below CUT threshold. 
			(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,differentPathConstraints)
			return (graphSat, synPaths)

		# Graph Partitioned in two. Apply Optimistic Synthesis on both of them. 
		# Propagate the first graph solutions as constraints to second. 

		# Create the Graphs.
		rcGraph1 = nx.Graph()
		rcGraph2 = nx.Graph()

		rc1empty = True
		rc2empty = True
		i = 0

		# # For testing, take input from user about partition. 
		# pclist = []
		# for node in rcGraph.nodes():
		# 	pclist.append(int(node))

		# print "Enter Partition for " + str(pclist)
		# s = raw_input()
		# partitions = map(int, s.split())

		OptimisticSolCount1 = 0
		OptimisticSolCount2 = 0

		for node in rcGraph.nodes():
			pc = int(node)
			solCount = 0
			
			# Find Optimistic paths which are isolated to pc. 
			isolatedPcs = self.pdb.getIsolatedPolicies(pc)
			for ipc in isolatedPcs :
				if ipc in self.OptimisticPaths : 
					solCount += 1

			if partitions[i] == 0 :
				rcGraph1.add_node(int(rcGraph.node[pc]['switch']), switch=str(rcGraph.node[pc]['switch'])) 
				rc1empty = False
				OptimisticSolCount1 += solCount

			elif partitions[i] == 1 :
				rcGraph2.add_node(int(rcGraph.node[pc]['switch']), switch=str(rcGraph.node[pc]['switch'])) 
				rc2empty = False
				OptimisticSolCount2 += solCount
			i += 1

		if rc1empty == True or rc2empty == True: 
			print "Cannot be partitioned"
			# Cannot partition the graph further. Apply synthesis. 
			(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,differentPathConstraints)
			return (graphSat, synPaths)

		for edge in rcGraph.edges() :
			if edge[0] in rcGraph1.nodes() and edge[1] in rcGraph1.nodes() :
				# Internal edge. Add to rcGraph1.
				rcGraph1.add_edge(*edge)
			elif edge[0] in rcGraph2.nodes() and edge[1] in rcGraph2.nodes() :
				# Internal edge. Add to rcGraph1.
				rcGraph2.add_edge(*edge)
		
		# Decide on the order of RCgraph1 and RCgraph2. We must synthesize the graph which has more constraints 
		# and then the one with less constraints. 
		if OptimisticSolCount1 < OptimisticSolCount2 : 
			# Swap the order of graphs.
			rcGraph1, rcGraph2 = rcGraph2, rcGraph1
			print "Swapping the order."
	

		(rcGraph1Sat, synPaths1) = self.enforceGraphPoliciesOptimistic(rcGraph1, differentPathConstraints)

		if rcGraph1Sat == False : 
			# Function cannot find a solution on the complete graph, as partial graph failed.
			return (False, synPaths1)  # synPaths1 is the unsat cores that failed the synthesis of rcGraph1.

		(rcGraph2Sat, synPaths2) = self.enforceGraphPoliciesOptimistic(rcGraph2, differentPathConstraints)

		if rcGraph2Sat == True : 
			# Partial graph solutions can be combined. 
			synPaths1.update(synPaths2)
			return (True, synPaths1)
		else : 
			if self.recoveryFlag == False :
				print "Program failed to find a solution"
				#exit(0)
			# Recovery can be performed at this level, as additional constraints failed the solution.
			# We try to find another solution for rcGraph1 and then apply synthesis of rcGraph2.
			if differentPathConstraints == None :
				localDifferentPathConstraints = []
			else : 
				localDifferentPathConstraints = list(differentPathConstraints)

			unsatCorePathConstraints = []
			for pc in synPaths2.keys() :
				path = synPaths2[pc]
				unsatCorePathConstraints.append([pc, path])
			localDifferentPathConstraints.append(unsatCorePathConstraints)

			# Pruning the different solutions to include only the relevant ones. 
			localDifferentPathConstraints = self.pruneDifferentPathConstraints(localDifferentPathConstraints, rcGraph1)

			if len(localDifferentPathConstraints) == 0 :
				# Cannot perform recovery at this level as none of the unsat core paths belong to rcGraph1.
				return (False, synPaths2) # SynPaths returns the unsat core paths. 

			# Attempt different solution recovery. 
			(recoverySat, synPaths) = self.differentSolutionRecovery(self.DIFF_SOL_RETRY_COUNT, rcGraph1, rcGraph2, localDifferentPathConstraints)

			if recoverySat == True :
				return (recoverySat, synPaths)
			else :
				# If recovery did not work, do not partition the graph.
				return self.enforceGraphPolicies(rcGraph,differentPathConstraints)

	def prunePathIsolationConstraints(self, pathConstraints) :
		"""Removes duplicate path constraints"""
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

	def pruneDifferentPathConstraints(self, differentPathConstraints, rcGraph) :
		pclist = []
		for node in rcGraph.nodes() :
			pclist.append(int(node))

		newPathConstraints = []
		for unsatCore in differentPathConstraints :
			prunedUnsatCore = []
			for pathConstraint in unsatCore : 
				if pathConstraint[0] in pclist :
					prunedUnsatCore.append(pathConstraint)
			if len(prunedUnsatCore) > 0 :
				newPathConstraints.append(prunedUnsatCore)
		
		return newPathConstraints

	def differentSolutionRecovery(self, attempt, rcGraph1, rcGraph2, differentPathConstraints) :
		print "Recovery Attempt #" + str(attempt) + " " + str(differentPathConstraints)
		if differentPathConstraints == None :
			localDifferentPathConstraints = []
		else : 
			localDifferentPathConstraints = list(differentPathConstraints)

		(rcGraph1Sat, synPaths1) = self.enforceGraphPoliciesOptimistic(rcGraph1, localDifferentPathConstraints)
			
		if rcGraph1Sat == False : 
			print "Recovery Failed"
			# Function cannot find a different solution. Stop different solution recovery. 
			return (False, dict())
			# Returning the empty dict because the failure of rcGraph1 is due to the absence of different solutions 
			# apart from the ones we found. Failure is not due to external isolate constraints. 

		(rcGraph2Sat, synPaths2) = self.enforceGraphPoliciesOptimistic(rcGraph2, differentPathConstraints)

		if rcGraph2Sat == True : 
			# Partial graph solutions can be combined. 
			synPaths1.update(synPaths2)
			return (True, synPaths1)
		else : 
			# Append the tried and failed solution to the different path list.
			if self.ResetOldSolutionsFlag == True :
				localDifferentPathConstraints = []

			unsatCorePathConstraints = []
			for pc in synPaths2.keys() :   # SynPaths2 provides the unsat core paths. 
				path = synPaths2[pc]
				unsatCorePathConstraints.append([pc, path])
			localDifferentPathConstraints.append(unsatCorePathConstraints)

			attempt = attempt - 1 # Decrease attempt number by 1.

			if attempt == 0 :
				# Different Solution Recovery could not find solution after 'n' attempts. 
				# Try to synthesise the rcGraphs pessimisticly. 
				(rcGraph1Sat, synPaths1) = self.enforceGraphPolicies(rcGraph1)
				if rcGraph1Sat == True : 
					(rcGraph2Sat, synPaths2) = self.enforceGraphPolicies(rcGraph2)
				return (False, dict())

			return self.differentSolutionRecovery(attempt, rcGraph1, rcGraph2, localDifferentPathConstraints)

	def linkcapacityRecovery(self, attempt, unsatLinks, rcGraph, differentPathConstraints) :
		self.pdb.printPaths(self.topology)
		# Remove atleast n flows flowing through the unsatLinks, and resynthesise rcGraph.
		pclist = []
		for node in rcGraph.nodes() :
			pclist.append(int(node))

		print "Perform link capacity recovery attempt#" + str(attempt) + " for " + str(pclist)
		print "UnsatLinks : " + str(unsatLinks)

		totalreroutes = 0
		for link in unsatLinks : 
			# Pick policies to reroute. 
			reroutedPCs = []
			key = str(link[0]) + "-" + str(link[1])
			trackedPCs = list(self.OptimisticTrackedPaths[key])
			print "Tracked PCs", trackedPCs

			while len(reroutedPCs) < len(pclist):
				# Find n best pplicies to reroute.
				bestpc = self.getBestReroutePacketClass(key, trackedPCs)
				if bestpc == None :
					break 
				else :
					successFlag = self.enforceReroute(bestpc, link[0], link[1])
					if successFlag : 
						reroutedPCs.append(bestpc)
				trackedPCs.remove(bestpc)

			totalreroutes = totalreroutes + len(reroutedPCs)

		if totalreroutes == 0 :
			# None of the pcs were rerouted. Recovery cannot be performed. 
			return False

		# For all unsatLinks, we have performed reroutes. Synthesise original graph.
		(rcGraphSat, synPaths) = self.enforceGraphPolicies(rcGraph, differentPathConstraints, False) 
		# Do not perform recovery in this, as we are already in recovery. 

		if rcGraphSat == True :
			return True
		else : 
			# perform recovery on updated unsat Link cores. 
			attempt = attempt - 1
			if attempt == 0 : 
				return False

			# Call recovery
			return self.linkcapacityRecovery(attempt, self.OptimisticUnsatLinkCores, rcGraph, differentPathConstraints)
			 
	def getBestReroutePacketClass(self, linkKey, pclist) :
		# Returns the best packet class (least degree and unrerouted).
		if (len(pclist)) == 0 :
			return None
		print pclist
		minpc = pclist[0]
		mindegree = self.pdb.getRelationalClassGraphDegree(minpc)
		for pc in pclist :
			degree = self.pdb.getRelationalClassGraphDegree(pc)
			if pc in self.OptimisticLinkRecoveryAttempts: 
				if linkKey in self.OptimisticLinkRecoveryAttempts[pc] :
					continue

			# compare with mindegree
			if degree < mindegree :
				minpc = pc
				mindegree = degree

		# Check if minimum is valid (no reroute attempt)
		if minpc in self.OptimisticLinkRecoveryAttempts: 
			if linkKey in self.OptimisticLinkRecoveryAttempts[minpc] :
				# There is no valid pc to return. Return None.
				return None

		# minpc will be used in the recovery. Add attempt for linkKey.
		if minpc in self.OptimisticLinkRecoveryAttempts:
			self.OptimisticLinkRecoveryAttempts[minpc].append(linkKey)
		else :
			self.OptimisticLinkRecoveryAttempts[minpc] = [linkKey]
		print self.OptimisticLinkRecoveryAttempts[minpc]
		return minpc

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
					#self.z3Solver.add(ForAll(self.pc, self.F(sw,s,self.pc,1) == False))
					self.z3Solver.add(ForAll(self.pc, self.Fwd(sw,s,self.pc) == False))

	def addTopologyConstraintsSAT(self, pcStart, pcEnd=0) :
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
						#neighbourAssert = self.F(sw,n,pc,1) == True
						neighbourAssert = self.Fwd(sw,n,pc) == True
						unreachedAssert = And(unreachedAssert, self.Fwd(sw,n,pc) == False)
						for n1 in neighbours :
							if n == n1 : 
								continue
							else :
								neighbourAssert = And(neighbourAssert, self.Fwd(sw,n1,pc) == False)
						topoAssert = Or(topoAssert, neighbourAssert)

					topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
					self.z3Solver.add(topoAssert)
				else :
					""" Multicast packet class. No restrictions on forwarding set """
					pass	

	def addTopologyConstraints(self, pcStart, pcEnd=0) :
		if self.UseTopoSAT == True :
			self.addTopologyConstraintsSAT(pcStart, pcEnd)
			return

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

					fname = "fwdSet" + str(sw) + "#" + str(pc)
					fwdSet = Function(fname, IntSort(), IntSort(), IntSort(), IntSort())

					i = 0
					for n in neighbours :
						if n == neighbours[0] :
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc), fwdSet(sw, pc, n) == 1))
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc) == False, fwdSet(sw, pc, n) == 0))
						else :
							prevn = neighbours[i - 1]
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc), fwdSet(sw, pc, n) == 1 + fwdSet(sw, pc, prevn)))
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc) == False, fwdSet(sw, pc, n) == fwdSet(sw, pc, prevn)))
						i +=1
					n = neighbours[i - 1] # Last element in the list.
					self.z3Solver.add(fwdSet(sw, pc, n) < 2)
				else :
					""" Multicast packet class. No restrictions on forwarding set """
					pass	

	def addTopologySliceConstraints(self, slice, pcStart, pcEnd=0) :
		if pcEnd == 0 :
			""" Topology Constraint for one packet class"""
			pcEnd = pcStart + 1

		topologySlice = self.topology.getTopologySlice(slice)
		# \forall sw \forall n \in neighbours(sw) and NextHop = {n | F(sw,n,pc,1) = True}. |NextHop| \leq 1 
		# None or only one of F(sw,n,pc,1) can be true.
		for sw in topologySlice :
			for pc in range(pcStart, pcEnd) :
				if not self.pdb.isMulticast(pc) : 
					""" Unicast packet class """
					neighbours = self.topology.getSwitchNeighbours(sw)

					# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
					topoAssert = False
					unreachedAssert = True

					for n in neighbours : 
						#neighbourAssert = self.F(sw,n,pc,1) == True
						neighbourAssert = self.Fwd(sw,n,pc) == True
						unreachedAssert = And(unreachedAssert, self.Fwd(sw,n,pc) == False)
						for n1 in neighbours :
							if n == n1 : 
								continue
							else :
								neighbourAssert = And(neighbourAssert, self.Fwd(sw,n1,pc) == False)
						topoAssert = Or(topoAssert, neighbourAssert)

					topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
					self.z3Solver.add(topoAssert)
				else :
					""" Multicast packet class. No restrictions on forwarding set """
					pass

	def addReachabilityConstraints(self, srcIP, srcSw, dstIP, dstSw, pc, W=None, pathlen=0) :
		if pathlen == 0 :
			# Default argument. Set to max.
			pathlen = self.topology.getMaxPathLength()

		# Specific case for a fat tree to apply path length upper bounds. 
		if self.fatTreeOptimizeFlag :
			pathlen = self.fatTreePathLengthOptimizations(W)
		
		# Add Reachability in atmost pathlen steps constraint. 
		reachAssert = self.Reach(dstSw,pc,pathlen) == True
		self.z3Solver.add(reachAssert)

		# At Destination, forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(dstSw)
		
		destAssert = True
		for n in neighbours :
			destAssert = And(destAssert, self.Fwd(dstSw,n,pc) == False)

		self.z3Solver.add(destAssert)

		if not W == None : 
			print W
			# Add the Waypoint Constraints. 
			for w in W :
				reachAssert = self.Reach(w,pc,pathlen) == True
				self.z3Solver.add(reachAssert)

		st = time.time()
		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addPathConstraints(srcSw,pc)		
		et = time.time()
		#tprint "Path Constraints time is " + str(et - st)
		
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

	# Note This functions take the most time for each pc. Look for ways to improve this
	def addPathConstraints(self, s, pc) :
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()

		if self.topologySlicingFlag : 
			swList = self.topology.getTopologySlice(self.topology.getSliceNumber(s))
		else : 
			swList = range(1,swCount + 1)
		
		# Base case connecting Fwd and Reach
		neighbours = self.topology.getSwitchNeighbours(s)
		for n in neighbours :
			# If Fwd rule exists means we can reach in path length 1.
			self.z3Solver.add(Implies(self.Fwd(s,n,pc), self.Reach(n,pc,1)))
		
		for i in swList:
			if i == s : continue
			self.z3Solver.add(Implies(self.Reach(i,pc,1), self.Fwd(s,i,pc)))

		# Add assertions to ensure f(s,*) leads to a valid neighbour. 
		neighbourAssert = False
		for n in neighbours :
			neighbourAssert = Or(neighbourAssert, self.Fwd(s,n,pc) == True)

		self.z3Solver.add(neighbourAssert)

		# Existence of a rule only when we can reach node. 
		for i in swList :
			if i == s : 
				continue

			ineighbours = self.topology.getSwitchNeighbours(i)
			for isw in ineighbours :
				ruleAssert = Implies(self.Fwd(i,isw,pc), self.Reach(i,pc,maxPathLen))
				self.z3Solver.add(ruleAssert)

		st = time.time()
		for i in swList :
			if i == s : 
				continue

			for pathlen in range(2,maxPathLen+1) :	
				reachedAssert = (Implies (self.Reach(i,pc,pathlen-1), self.Reach(i,pc,pathlen)))
				self.z3Solver.add(reachedAssert)
	
		#tprint "Path1 " + str(time.time() - st)
		st = time.time()

		for i in swList :
			if i == s : 
				continue

			ineighbours = self.topology.getSwitchNeighbours(i) 
			neighbourAssert = False

			if self.UseQuantifiersflag :
				for isw in ineighbours : 
					plen = Int("plen" + "#" + str(i) + "#" + str(isw))
					nextHopAssert = Implies(And(self.Reach(i,pc,plen) == True,self.Fwd(i,isw,pc) == True),self.Reach(isw,pc,plen + 1) == True)
					self.z3Solver.add(ForAll(plen, nextHopAssert))
			else :
				for isw in ineighbours : 
					for pathlen in range(1,maxPathLen) :
						nextHopAssert = Implies(And(self.Reach(i,pc,pathlen) == True,self.Fwd(i,isw,pc) == True),self.Reach(isw,pc,pathlen+1) == True)
						self.z3Solver.add(nextHopAssert)
				

		#tprint "Path2 " + str(time.time() - st)
		st = time.time()

		for i in swList :
			if i == s : 
				continue

			ineighbours = self.topology.getSwitchNeighbours(i) 

			# Paths of length 2.
			path2Assert = True
			for pathlen in range(2,maxPathLen+1) :
				beforeHopAssert = False
				for isw in ineighbours : 
					beforeHopAssert = Or(beforeHopAssert, And(self.Fwd(isw, i, pc) == True, self.Reach(isw, pc, pathlen - 1) == True))
				
				path2Assert = And(path2Assert, Implies(self.Reach(i,pc,pathlen), beforeHopAssert))

			# beforeHopAssert = False
			# for isw in ineighbours : 
			# 	beforeHopAssert = Or(beforeHopAssert, And(self.F(isw, i, pc, 1) == True, self.F(s, isw, pc, pathlen - 1) == True))
			
			# plen = Int('plen')
			# path2Assert = ForAll(plen, Implies(And(plen > 1, plen < maxPathLen, self.F(s,i,pc,pathlen)), beforeHopAssert))

			path1Assert = self.Fwd(s,i,pc) == True
			self.z3Solver.add(Or(path1Assert, path2Assert))

		for i in swList :
			# Path len > 1 always.
			self.z3Solver.add(self.Reach(i,pc,0) == False)

		for i in swList :
			if i == s : 
				continue

			# if Fwd rule exists, node should be reachable.
			ineighbours = self.topology.getSwitchNeighbours(i)

			for isw in ineighbours :
				self.z3Solver.add(Implies(self.Fwd(i,isw,pc), self.Reach(i,pc,maxPathLen)))

		#tprint "Path3 " + str(time.time() - st)
		st = time.time()

	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """

		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.Fwd(sw,n,pc1) == True, self.Fwd(sw,n,pc2) == True))
				self.z3Solver.add(isolateAssert)	

	def addSliceTrafficIsolationConstraints(self, slice, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """

		swList = self.topology.getTopologySlice(slice)
		for sw in swList :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.Fwd(sw,n,pc1) == True, self.Fwd(sw,n,pc2) == True))
				self.z3Solver.add(isolateAssert)	

	def addPathIsolationConstraints(self, pc, path, tracker=0) :
		""" Adding constraints such that the path of pc is isolated by 'path' argument"""
		i = 0
		pathIsolateAssert = True
		for i in range(len(path) - 1) :
			pathIsolateAssert = And(pathIsolateAssert, self.Fwd(path[i], path[i+1], pc) == False)
		self.z3Solver.assert_and_track(pathIsolateAssert, str(tracker))

	def addSlicePathIsolationConstraints(slice, pc, path, tracker=0) :
		""" Adding constraints such that the path of pc is isolated by 'path' argument in the slice."""
		i = 0
		pathIsolateAssert = True
		for i in range(len(path) - 1) :
			if self.topology.getSliceNumber(path[i]) == slice and self.topology.getSliceNumber(path[i+1]) == slice :
				pathIsolateAssert = And(pathIsolateAssert, self.Fwd(path[i], path[i+1], pc) == False)
		self.z3Solver.assert_and_track(pathIsolateAssert, str(tracker))
			

	def addDifferentPathConstraint(self, pc, path) :
		""" Adding constraint such that pc finds a solution different from path"""
		i = 0
		diffPathAssert = True
		for i in range(len(path) - 1) :
			diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc) == True)

		self.z3Solver.add(Not(diffPathAssert))

	def addDifferentSolutionConstraint(self, pathConstraints) :
		""" Adding constraints such that the solution obtained is different from the solution provided by arg pathConstraints
			pathConstraints = List of [pc, path]"""
		diffPathAssert = True
		for pathConstraint in pathConstraints :
			i = 0
			pc = pathConstraint[0]
			path = pathConstraint[1]
			for i in range(len(path) - 1) :
				diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc) == True)

		self.z3Solver.add(Not(diffPathAssert))

	def addSliceDifferentSolutionConstraint(self, slice, pathConstraints) :
		""" Adding constraints such that the solution obtained is different from the solution provided by arg pathConstraints
			pathConstraints = List of [pc, path]"""
		diffPathAssert = True
		for pathConstraint in pathConstraints :
			i = 0
			pc = pathConstraint[0]
			path = pathConstraint[1]
			for i in range(len(path) - 1) :
				if self.topology.getSliceNumber(path[i]) == slice and self.topology.getSliceNumber(path[i+1]) == slice :
					diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc) == True)

		self.z3Solver.add(Not(diffPathAssert))

	def enforceReroute(self, pc, sw1, sw2) :
		""" Resynthesise path for pc so that it does not go through link sw1-sw2 """
		oldpath = list(self.OptimisticPaths[pc])
		# Revert oldpath changes : 
		for constraint in self.OptimisticLinkCapacityConstraints : 
			try : 
				index = oldpath.index(constraint[0])
				if index == len(oldpath) - 1:
					continue # Last element. 
				if oldpath[index + 1] == constraint[1] :
					# Link was used. Increment constraint.
					constraint[2] = constraint[2] + 1

				# Remove pc from tracked paths.
				key = str(constraint[0]) + "-" + str(constraint[1]) 
				if key in self.OptimisticTrackedPaths : 
					if pc in self.OptimisticTrackedPaths[key] :
						self.OptimisticTrackedPaths[key].remove(pc)
			except ValueError:
					continue

		self.z3Solver.push()

		policy = self.pdb.getReachabilityPolicy(pc)
		self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

		# Add Topology Constraints
		self.addTopologyConstraints(pc)

		# Add Isolation Constraints 
		for pno in range(self.pdb.getIsolationPolicyCount()) :
			pcs = self.pdb.getIsolationPolicy(pno)
			pc1 = pcs[0]
			pc2 = pcs[1]
			if pc1 == pc and pc2 in self.OptimisticPaths: 
				self.addPathIsolationConstraints(pc1, self.OptimisticPaths[pc2], pc2)
			elif pc2 == pc and pc1 in self.OptimisticPaths:
				self.addPathIsolationConstraints(pc2, self.OptimisticPaths[pc1], pc1)

		# Add Reroute Constraint. 
		self.z3Solver.add(self.Fwd(sw1, sw2, pc) == False)

		# Add Link Capacity Constraints : 
		self.addLinkConstraints([pc], self.OptimisticLinkCapacityConstraints)

		successFlag = False
		modelsat = self.z3Solver.check()
		if modelsat == z3.sat : 
			successFlag = True
			print "Reroute successful : SAT", pc
			self.fwdmodel = self.z3Solver.model()
			path = self.getPathFromModel(pc)
			self.pdb.addPath(pc, path)
			self.OptimisticPaths[pc] = path

			print "Old path", oldpath, "new path", path
			# Reset isolated policies (can be reattempted for reroute)
			self.OptimisticLinkRecoveryAttempts[pc] = []
			isolatedPcs = self.pdb.getIsolatedPolicies(pc)
			for ipc in isolatedPcs : 
				self.OptimisticLinkRecoveryAttempts[ipc] = []
		else :
			# Rerouting not possible. 
			path = oldpath

		# Update Optimistic link capacity constraints.
		for constraint in self.OptimisticLinkCapacityConstraints : 
			try:
				index = path.index(constraint[0])
				if index == len(path) - 1:
					continue # Last element. 
				if path[index + 1] == constraint[1] :
					# Link is used. Update constraint.
					constraint[2] = constraint[2] - 1
				
				# Add pc to tracked Paths. 
				key = str(constraint[0]) + "-" + str(constraint[1])
				if key in self.OptimisticTrackedPaths : 
					self.OptimisticTrackedPaths[key].append(pc)
				else : 
					self.OptimisticTrackedPaths[key] = [pc]
			except ValueError:
				continue

		self.z3Solver.pop()

		return successFlag

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
	
	def addSwitchTableConstraints(self, constraints) :
		if len(constraints) == 0 : return
		""" Constraints : List of [switch-name, max-size]"""

		for pc in range(self.pdb.getPacketClassRange()) :
			src = self.pdb.getSourceSwitch(pc)
			dst = self.pdb.getDestinationSwitch(pc)
			swCount = self.topology.getSwitchCount()
			maxPathLen = self.topology.getMaxPathLength()

			if pc == 0: 
				for i in range(1,swCount+1) : 
					if not i == dst : 
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == True, self.R(i, pc) == 1))
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == False, self.R(i, pc) == 0))
					else :
						self.z3Solver.add(self.R(i, pc) == 0)
			else :
				for i in range(1,swCount+1) :
					if not i == dst :
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == True, self.R(i, pc) == self.R(i, pc-1) + 1))
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == False, self.R(i, pc) == self.R(i, pc-1)))
					else :
						self.z3Solver.add(self.R(i, pc) == self.R(i, pc-1))

		maxpc = self.pdb.getPacketClassRange() - 1
		for constraint in constraints :
			sw = constraint[0]
			self.z3Solver.add(self.R(sw, maxpc) < constraint[1] + 1)

	def addLinkConstraints(self, pclist, constraints):
		if len(constraints) == 0 : return
		""" Constraints : List of [sw1, sw2, max-number-of-flows]"""

		pclist.sort()
		maxpc = pclist[len(pclist) - 1] # Max pc in pclist
		for constraint in constraints :
			sw1 = constraint[0]
			sw2 = constraint[1]
			tracker = str(sw1) + "-" + str(sw2)
			self.z3Solver.assert_and_track(self.L(sw1, sw2, maxpc) < constraint[2] + 1, tracker)

		i = 0
		for pc in pclist :
			for constraint in constraints :
				sw1 = constraint[0]
				sw2 = constraint[1]

				if i == 0 :
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == True, self.L(sw1, sw2, pc) == 1))
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == False, self.L(sw1, sw2, pc) == 0))
				else :
					prevpc = pclist[i - 1]
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == True, self.L(sw1, sw2, pc) == self.L(sw1, sw2, prevpc) + 1))
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == False, self.L(sw1, sw2, pc) == self.L(sw1, sw2, prevpc)))
			i += 1

	def getPathFromModel(self, pc) :
		def getPathHelper(s, pc) :
			path = [s]
			swCount = self.topology.getSwitchCount()
			
			for sw in range(1, swCount + 1) :
				if sw == s : 
					continue
				if is_true(self.fwdmodel.evaluate(self.Fwd(s,sw,pc))) :
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
				if is_true(self.fwdmodel.evaluate(self.Fwd(s,sw,pc))) :
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

	def enforceChangedPolicies(self):
		# A model already exists. Synthesis of newly added policies. 
		self.addTopologyConstraints(0, self.pdb.getPacketClassRange())

		#create the updated relational Classes.
		self.pdb.createRelationalClasses()
		relClasses = self.pdb.getUnenforcedRelationalClasses()
		print relClasses

		# Naive synthesis approach : Apply enforced policies as constraints to the unenforced ones.
		for relClass in relClasses:
			self.z3Solver.push()
			for pc in relClass :
				if not self.pdb.isEnforced(pc): 
					if not self.pdb.isMulticast(pc) :  
						policy = self.pdb.getReachabilityPolicy(pc)
						print policy
						self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

			# Add traffic constraints. 
			for pno in range(self.pdb.getIsolationPolicyCount()) :
				pc = self.pdb.getIsolationPolicy(pno)
				pc1 = pc[0]
				pc2 = pc[1]
				if pc1 in relClass and pc2 in relClass : 
					if self.pdb.isEnforced(pc1) and self.pdb.isEnforced(pc2) :
						continue
					elif self.pdb.isEnforced(pc1) :
						self.addPathIsolationConstraints(pc2, self.pdb.getPath(pc1), pc1)
					elif self.pdb.isEnforced(pc2) :
						self.addPathIsolationConstraints(pc1, self.pdb.getPath(pc2), pc2)
					else :
						self.addTrafficIsolationConstraints(pc1, pc2)

			#self.addSwitchTableConstraints()  # Adding switch table constraints.
						
			# Each relational class can be synthesised independently.
			modelsat = self.z3Solver.check()
			if modelsat == z3.sat : 
				print "SAT"
				self.fwdmodel = self.z3Solver.model()
				for pc in relClass :
					if not self.pdb.isEnforced(pc) :
						self.pdb.addPath(pc, self.getPathFromModel(pc))	
			else :
				print "Input Policies not realisable"

			self.z3Solver.pop()

		self.pdb.printPaths(self.topology)

	def enforceSliceGraphPolicies(self, slice, rcGraph, differentPathConstraints=None) :
		""" Synthesis of the Relational Class Graph given some path constraints (isolation and inequality) on the slice.
		If True, return the sat core paths for the RC Graph. 
		If False, return the unsat core paths to aid search for different constraints of isolation"""

		synPaths = dict()
		unsatLinks = []

		self.z3Solver.push()

		st = time.time()
		#tprint "Adding constraints."
		pclist = []
		for node in rcGraph.nodes() :
			pclist.append(int(node))

		if len(pclist) == 0 :
			print "Function should not be called on empty graph."
			#exit(0)

		for pc in pclist : 
			if not self.pdb.isMulticast(pc) :  
				policy = self.pdb.getSliceReachabilityPolicy(pc)
				st = time.time()
				self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1]) 
				#tprint "Time taken to add Reachability constraints is " + str(time.time() - st)
				
				if not self.addGlobalTopoFlag : 
					st = time.time()
					# Add Topology Slice Constraints
					self.addTopologySliceConstraints(slice, pc)
					#tprint "Time taken to add Topology constraints is " + str(time.time() - st)

		# Add local traffic constraints. 
		for edge in rcGraph.edges() :
			self.addTrafficIsolationConstraints(edge[0], edge[1])

		# Add Optimistic Traffic Constraints.
		for pc in pclist : 
			ipcs = self.pdb.getIsolatedPolicies(self.pdb.getOriginalPacketClass(pc))
			for ipc in ipcs :
				if ipc in self.OptimisticPaths : 
					self.addSlicePathIsolationConstraints(slice, pc, self.OptimisticPaths[ipc], ipc)


		if not differentPathConstraints == None : 
			# Unsat Cores: [pc1, path]. pc1 must find a solution which is not equal to path. 
			for unsatCores in differentPathConstraints : 
				self.addSliceDifferentSolutionConstraint(unsatCores)
				
		# Add link capacity constraints.  (Ignore for now)
		#self.addLinkConstraints(pclist, self.OptimisticLinkCapacityConstraints)

		print "Starting Z3 check for " + str(pclist)
		st = time.time()
		modelsat = self.z3Solver.check()
		if modelsat == z3.sat : 
			#tprint "Time taken to solve the constraints is " + str(time.time() - st)
			rcGraphSat = True
			print "SAT"
			self.fwdmodel = self.z3Solver.model()
			for pc in pclist :
				path = self.getPathFromModel(pc)
				synPaths[pc] = path

		else :
			rcGraphSat = False
			print "Input Policies not realisable"
		
		self.z3Solver.pop()
		return (rcGraphSat, synPaths)

	def applyTopologySlicing(self, rcGraph, differentPathConstraints=None) :
		self.topology.useTopologySlicing()
		self.topology.createSliceGraph()

		slicePaths = dict()
		pclist = []
		for node in rcGraph.nodes() :
			pc = int(node)
			pclist.append(pc)
			slicePaths[pc] = dict()

		(rcGraphs, splitReachPolicyEdges, sliceGraphPaths) = self.createSliceRelationalGraphs(pclist)

		for slice in rcGraphs.keys() :
			rcGraph = rcGraphs[slice]
			(rcGraphSat, synPaths) = self.enforceSliceGraphPolicies(slice, rcGraph, differentPathConstraints)

			if rcGraphSat == True :
				for pc in synPaths : 
					originalpc = self.pdb.getOriginalPacketClass(pc)
					self.addSlicePath(slicePaths[originalpc], synPaths[pc], sliceGraphPaths[originalpc])
			else : 
				print "Topology Slicing Failed. Exit Now!"
				exit(0)

		for pc in pclist : 
			path = self.getCompletePath(pc, slicePaths[pc], sliceGraphPaths[pc], splitReachPolicyEdges[pc])
			self.pdb.addPath(pc, path)
			self.OptimisticPaths[pc] = path

		# Clear intermediate split Reachability Policies.
		self.pdb.clearSliceReachabilityPolicies() 
			
		return (True, dict())


	def createSliceRelationalGraphs(self, pclist) :
		""" Splits the reachabilty policies in pclist and returns a Relational Class graph"""
		
		sliceEdgeMappings = dict()
		sliceGraphPaths = dict()
		for pc in pclist: 
			# Find path in slice graph.
			src = self.pdb.getSourceSwitch(pc)
			dst = self.pdb.getDestinationSwitch(pc)
			srcSlice = self.topology.getSliceNumber(src)
			dstSlice = self.topology.getSliceNumber(dst)

			if srcSlice == dstSlice : 
				sliceGraphPaths[pc] = []
				continue
			
			slicePath = []
			paths = self.topology.getSliceGraphPaths(srcSlice, dstSlice)

			for path in paths : 
				# pick shortest path. 
				if slicePath == [] : slicePath = path
				if len(path) < len(slicePath) :
					slicePath = path
			sliceGraphPaths[pc] = slicePath

			ipcs = self.pdb.getIsolatedPolicies(pc)
			i = 0

			while i < len(slicePath) - 1:
				sliceEdges = self.topology.getSliceEdges(slicePath[i], slicePath[i+1])
				for edge in sliceEdges : 
					# Check if edge is used by an optimistic path.
					edgeUsedFlag = False
					for ipc in ipcs : 
						if ipc in self.OptimisticPaths : 
							opath = self.OptimisticPaths[ipc]
							j = 0 
							while j < len(opath) - 1:
								if opath[j] == edge[0] and opath[j+1] == edge[1] :
									edgeUsedFlag = True
									break

					if edgeUsedFlag == False :
						# Can use this edge.
						key = str(edge[0]) + "-" + str(edge[1])
						if key in sliceEdgeMappings : 
							sliceEdgeMappings[key].append(pc)
						else : 
							sliceEdgeMappings[key] = [pc]
				i += 1

		reachPolicies = dict()
		mappingCount = dict()
		sliceEdgeList = [] # Store relevant slice edges for this rcGraph.

		for path in sliceGraphPaths.values():
			i = 0
			while i < len(path) - 1:
				sedge = str(path[i]) + "-" + str(path[i+1])
				if sedge not in sliceEdgeList :
					sliceEdgeList.append(sedge)
				i += 1

		print sliceEdgeList
		
		sliceEdgeCount = dict()
		for pc in pclist : 
			sliceEdgeCount[pc] = dict()

		for sedge in sliceEdgeList : 
			slice1 = int(sedge.split("-")[0])
			slice2 = int(sedge.split("-")[1])
			
			for pc in pclist : 
				for edgeKey in sliceEdgeMappings.keys() :
					edge = edgeKey.split("-") 
					if slice1 == self.topology.getSliceNumber(int(edge[0])) and slice2 == self.topology.getSliceNumber(int(edge[1])) and pc in sliceEdgeMappings[edgeKey]: 

						if sedge in sliceEdgeCount[pc] : 
							sliceEdgeCount[pc][sedge] += 1
						else :
							sliceEdgeCount[pc][sedge] = 1

		splitReachPolicyEdges = dict()
		for sedge in sliceEdgeList : 
			slice1 = int(sedge.split("-")[0])
			slice2 = int(sedge.split("-")[1])

			pclistUnmapped = []
			# Add relevant pcs to the list
			for pc in pclist : 
				if sedge in sliceEdgeCount[pc] :
					pclistUnmapped.append(pc)

			while len(pclistUnmapped) > 0 :
				mincount = 100000
				for pc in pclistUnmapped : 
					if mincount > sliceEdgeCount[pc][sedge] : 
						mincount = sliceEdgeCount[pc][sedge]
						minpc = pc

				if mincount == 0 :
					print "Mapping does not exist!" 
					exit(0)

				print "Mapping minpc", minpc, "for sedge", sedge
				# Found minpc. Map one edge for this slice-edge to this pc.
				for edgeKey in sliceEdgeMappings.keys() :
					edge = edgeKey.split("-") 
					if slice1 == self.topology.getSliceNumber(int(edge[0])) and slice2 == self.topology.getSliceNumber(int(edge[1])) and minpc in sliceEdgeMappings[edgeKey]: 
						# Map this edge to sliceEdgeMapping. 
						affectedpcs = sliceEdgeMappings[edgeKey]
						sliceEdgeMappings[edgeKey] = []
						
						if minpc in splitReachPolicyEdges : 
							splitReachPolicyEdges[minpc].append(edgeKey)
						else : 
							splitReachPolicyEdges[minpc] = [edgeKey]

						# Remove minpc from Unmapped pcs
						pclistUnmapped.remove(minpc)
						# Decrement count of affectedpcs
						for apc in affectedpcs :
							if apc == minpc : continue
							else : sliceEdgeCount[pc][sedge] -= 1

						break
		print splitReachPolicyEdges

		rcGraphs = dict()
		# Build the slice RC Graphs. 
		for pc in pclist: 
			slicePath = sliceGraphPaths[pc] 
			if slicePath == [] : 
				# No split of reach policy.
				slice = self.topology.getSliceNumber(self.pdb.getSourceSwitch(pc))
				if slice in rcGraphs : 
					rcGraphs[slice].add_node(pc, switch=str(pc))
				else : 
					rcGraphs[slice] = nx.Graph()
					rcGraphs[slice].add_node(pc, switch=str(pc))
			else :
				# Slice path exists. 
				src = self.pdb.getSourceSwitch(pc)
				srcSlice = self.topology.getSliceNumber(src)

				i = 0
				print slicePath
				while i < len(slicePath) - 1:
					nextSlice = slicePath[i + 1]

					for edgeKey in splitReachPolicyEdges[pc] :
						edge = edgeKey.split("-")
						if self.topology.getSliceNumber(int(edge[0])) == srcSlice and self.topology.getSliceNumber(int(edge[1])) == nextSlice : 
							if src == int(edge[0]) :
								print "Don't need to add anything.", src
							else :
								slicepc = self.pdb.addSliceReachabilityPolicy(pc, src, int(edge[0]))
								if srcSlice in rcGraphs : 
									rcGraphs[srcSlice].add_node(slicepc, switch=str(slicepc))
								else : 
									rcGraphs[srcSlice] = nx.Graph()
									rcGraphs[srcSlice].add_node(slicepc, switch=str(slicepc))
							
							srcSlice = nextSlice
							src = int(edge[1])
							break
					i += 1

				# Add Reachability to dst
				if not src == self.pdb.getDestinationSwitch(pc) : 
					slicepc = self.pdb.addSliceReachabilityPolicy(pc, src, self.pdb.getDestinationSwitch(pc))
					if srcSlice in rcGraphs : 
						rcGraphs[srcSlice].add_node(slicepc, switch=str(slicepc))
					else : 
						rcGraphs[srcSlice] = nx.Graph()
						rcGraphs[srcSlice].add_node(slicepc, switch=str(slicepc))

		# Adding policy edges in the rcGraphs.
		for rcGraph in rcGraphs.values() :
			pcs = []
			for node in rcGraph.nodes() :
				pcs.append(int(node))
			for pc1 in pcs : 
				for pc2 in pcs : 
					if pc1 >= pc2 :
						continue
					else :
						opc1 = self.pdb.getOriginalPacketClass(pc1)
						opc2 = self.pdb.getOriginalPacketClass(pc2)
						if self.pdb.isIsolated(opc1, opc2) :
							rcGraph.add_edge(pc1, pc2)

		return (rcGraphs, splitReachPolicyEdges, sliceGraphPaths)


	def addSlicePath(self, slicePath, path, sliceGraphPath) : 
		slice = self.topology.getSliceNumber(path[0])
		slicePath[sliceGraphPath.index(slice)] = path

	def getCompletePath(self, pc, slicePath, sliceGraphPath, sliceEdges) : 
		for i in range(len(sliceGraphPath)) : 
			if i not in slicePath and i == 0:
				slicePath[i] = [self.pdb.getSourceSwitch(pc)]
			if i not in slicePath and i > 0: 
				slice1 = sliceGraphPath[i-1]
				slice2 = sliceGraphPath[i]
				for edgeKey in sliceEdges : 
					edge = edgeKey.split("-")
					if self.topology.getSliceNumber(int(edge[0])) == slice1 and self.topology.getSliceNumber(int(edge[1])) == slice2 :
						slicePath[i] = [int(edge[1])]

		# Combine all paths to get complete Path.
		completePath = []
		for path in slicePath.values() :
			completePath.extend(path)
		return completePath



















# nuZ3
# maxSAT
# US Backbone, RocketFuelS