from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx
from SliceGraphSolver import SliceGraphSolver
from Tactic import *
import re
from subprocess import *
from collections import deque
from ZeppelinSynthesiser import ZeppelinSynthesiser


class GenesisSynthesiser(object) :
	def __init__(self, topo, Optimistic=True, TopoSlicing=False, pclist=None, useTactic=False, noOptimizations=False, BridgeSlicing=True, weakIsolation=False, controlPlane=False) :
		self.topology = topo

		# Network Forwarding Function
		#self.Fwd = Function('Fwd', IntSort(), IntSort(), IntSort(), BoolSort())
		# self.Reach = Function('Reach', IntSort(), IntSort(), IntSort(), BoolSort())

		# Packet Classes to be synthesized.
		self.stackfwdvars = dict()
		self.stackreachvars = dict()

		self.R = Function('R', IntSort(), IntSort(), IntSort())
		self.L = Function('L', IntSort(), IntSort(), IntSort(), IntSort())
		#self.delta = Function('delta', IntSort(), IntSort(), IntSort())
		self.pc = Int('pc') # Generic variable for packet classes
		
		self.z3Solver = Solver()
		self.z3Solver.set(unsat_core=True)
		#self.z3Solver.set("sat.phase", "always-false")
		self.fwdmodel = None 

		self.sliceGraphSolver = SliceGraphSolver()

		self.count = 20
		# Policy Database. 
		self.pdb = PolicyDatabase()
		
		# Optimistic Synthesis Variables
		self.OptimisticPaths = dict()  # Stores the solutions obtained during the Optimistic synthesis procedure. 
		self.OptimisticLinkCapacityConstraints = []
		
		# Store the different retry attempts for link capacity recovery to ensure we dont repeat solutions.
		self.OptimisticLinkRecoveryAttempts = dict() 
		self.OptimisticTrackedPaths = dict()
		self.OptimisticUnsatLinkCores = []

		# Optimistic Synthesis Constants. 
		self.CUT_THRESHOLD = 50
		self.BASE_GRAPH_SIZE_THRESHOLD = 10
		self.CURR_GRAPH_SIZE_THRESHOLD = 10
		self.MIN_GRAPH_THRESHOLD = 3

		# Different Solution Recovery Variables. 
		self.DIFF_SOL_RETRY_COUNT = 10
		self.ResetOldSolutionsFlag = False

		# Link Capacity Recovery Variables
		self.LINK_RECOVERY_COUNT = 4

		# Optimistic Synthesis Flags 
		self.noOptimizationsFlag = noOptimizations
		self.OptimisticSynthesisFlag = Optimistic
		self.recoveryFlag = False
		self.topologySlicingFlag = TopoSlicing
		self.bridgeSlicingFlag = BridgeSlicing
		self.synthesisSuccessFlag = True
		self.weakIsolationFlag = weakIsolation

		# SAT Encoding Flags
		self.UseQuantifiersflag = True

		self.UseTopoSAT = True
		self.addGlobalTopoFlag = False

		# Profiling Information.
		self.z3constraintTime = 0 # Time taken to create the constraints.
		self.z3addTime = 0 # Time taken to add the constraints.
		self.z3numberofadds = 0 # Count of adds.
		self.z3solveTime = 0 # Time taken to solve the constraints. 
		self.metisTime = 0	# Time taken to partition  the graphs.
		self.z3SolveCount = 0	# Count of z3 solve instances. 

		# Tactic variables 
		self.useTacticFlag = useTactic
		self.tactics = dict()

		# Constraint Stores
		self.backwardReachPropagationConstraints = dict()

		# BFS Global Variable.
		self.bfsLists = dict()
		for i in range(1, self.topology.getMaxPathLength() + 1) :
			self.bfsLists[i] = []

		# Repair Mode
		self.repairMode = False

		# Generate Control Plane
		self.controlPlaneMode = controlPlane
		self.zeppelinSynthesiser = ZeppelinSynthesiser(self)

		# SMT Variables
		#self.smtlib2file = open("genesis-z3-smt", 'w')

		# Initialize SMT LIB2 file. 
		#self.smtlib2file.write("; Genesis Generated SMT-LIB2 \n(set-info :status unknown)\n(set-logic QF_LIA)\n")


	def initializeSATVariables(self) :
		swCount = self.topology.getSwitchCount()
		pcRange = self.pdb.getPacketClassRange()
		maxPathLen = self.topology.getMaxPathLength()

		self.fwdvars = [[[0 for x in range(pcRange)] for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.reachvars = [[[0 for x in range(maxPathLen+1)] for x in range(pcRange)] for x in range(swCount + 1)]

		for sw1 in range(1,swCount+1):
			for sw2 in range(1,swCount+1):
				for pc in range(pcRange) :
					self.fwdvars[sw1][sw2][pc] = Bool(str(sw1)+"-"+str(sw2)+":"+str(pc))
					#self.smtlib2file.write("(declare-fun |" + str(str(sw1)+"-"+str(sw2)+":"+str(pc)) + "| () Bool)\n")

		for sw in range(1,swCount+1):
			for pc in range(pcRange) :
				for plen in range(1,maxPathLen +1) :
					self.reachvars[sw][pc][plen] = Bool(str(sw)+":"+str(pc)+":"+str(plen))
					#self.smtlib2file.write("(declare-fun |" + str(str(sw)+":"+str(pc)+"*"+str(plen)) + "| () Bool)\n")

	def Fwd(self, sw1, sw2, pc) :
		if self.pdb.getOriginalPacketClass(pc) <> pc : 
			neighbours = self.topology.getSwitchNeighbours(sw2)
			if sw1 not in neighbours : 
				return False
			else : 
				return self.stackfwdvars[pc][sw1][sw2]
		else : 
			neighbours = self.topology.getSwitchNeighbours(sw2)
			if sw1 not in neighbours : 
				return False
			else : 
				return self.fwdvars[sw1][sw2][pc]

	def FwdStr(self, sw1, sw2, pc):
		if self.pdb.getOriginalPacketClass(pc) <> pc : 
			neighbours = self.topology.getSwitchNeighbours(sw2)
			if sw1 not in neighbours : 
				return "false"
			else : 
				return "|" + str(str(sw1)+"-"+str(sw2)+":"+str(pc)) + "|"
		else : 
			neighbours = self.topology.getSwitchNeighbours(sw2)
			if sw1 not in neighbours : 
				return "false"
			else : 
				return "|" + str(str(sw1)+"-"+str(sw2)+":"+str(pc)) + "|"


	def Reach(self, sw, pc, plen) :
		if self.pdb.getOriginalPacketClass(pc) <> pc : 
			if plen == 0 :
				if sw == self.pdb.getSourceSwitch(pc) : 
					return True
				else : 
					return False
			return self.stackreachvars[pc][sw][plen]
		else : 
			if plen == 0 :
				if sw == self.pdb.getSourceSwitch(pc) : 
					return True
				else : 
					return False
			return self.reachvars[sw][pc][plen]

	def ReachStr(self, sw, pc, plen) :
		if self.pdb.getOriginalPacketClass(pc) <> pc : 
			if plen == 0 :
				if sw == self.pdb.getSourceSwitch(pc) : 
					return "true"
				else : 
					return "false"
			return "|" + str(str(sw)+":"+str(pc)+"*"+str(plen)) + "|"
		else : 
			if plen == 0 :
				if sw == self.pdb.getSourceSwitch(pc) : 
					return "true"
				else : 
					return "false"
			return "|" + str(str(sw)+":"+str(pc)+"*"+str(plen)) + "|"

	def pushSATVariables(self, pclist):
		swCount = self.topology.getSwitchCount()
		pcRange = self.pdb.getPacketClassRange()
		maxPathLen = self.topology.getMaxPathLength()

		for pc in pclist : 
			if self.pdb.getOriginalPacketClass(pc) <> pc : 
				# Need to add variables.
				self.stackfwdvars[pc] = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
				self.stackreachvars[pc] = [[0 for x in range(maxPathLen+1)] for x in range(swCount + 1)]

				for sw1 in range(1,swCount+1):
					for sw2 in range(1,swCount+1):
						self.stackfwdvars[pc][sw1][sw2] = Bool(str(sw1)+"-"+str(sw2)+":"+str(pc))

				for sw in range(1,swCount+1):
					for plen in range(1,maxPathLen +1) :
						self.stackreachvars[pc][sw][plen] = Bool(str(sw)+":"+str(pc)+":"+str(plen))

	def popSATVariables(self, pclist) :
		for pc in pclist :
			if self.pdb.getOriginalPacketClass(pc) <> pc : 
				del self.stackfwdvars[pc]
				del self.reachvars[pc]

	def enforcePolicies(self): 
		if self.bridgeSlicingFlag : 
			self.bridgeSlicingFlag = self.topology.findTopologyBridges()

		start_t = time.time()
		self.initializeSATVariables()

		# # Topology Slicing : 
		# if self.topologySlicingFlag : 
		# 	self.topology.createSliceGraph()
		# 	self.initializeSliceGraphSolver()

		# Enforce Tactics 
		if self.useTacticFlag : 
			#st = time.time()
			self.useTactic()
			#et = time.time()
			#print "Time taken to create tactic variables is ", et - st
		
		# Generate the assertions.
		self.pdb.createRelationalClasses()

		# st = time.time()
		# if(not self.OptimisticSynthesisFlag) or self.addGlobalTopoFlag :
		# 	self.addTopologyConstraints(0, self.pdb.getPacketClassRange())
		# print "Time to add global topology constraints", time.time() - st

	
		if self.OptimisticSynthesisFlag : 
			rcGraphs = self.pdb.getRelationalClassGraphs()

			# Add link capacity constraints
			self.OptimisticLinkCapacityConstraints = self.pdb.getLinkCapacityConstraints()

			for rcGraph in rcGraphs :
				rcGraphSat = False
				self.CURR_GRAPH_SIZE_THRESHOLD = self.BASE_GRAPH_SIZE_THRESHOLD # reset the graph size to base value.
				
				while rcGraphSat == False and self.CURR_GRAPH_SIZE_THRESHOLD < rcGraph.number_of_nodes() : 
					(rcGraphSat, synPaths) = self.enforceGraphPoliciesOptimistic(rcGraph)
					if rcGraphSat == False : 
						# Incremental Graph recovery
						self.CURR_GRAPH_SIZE_THRESHOLD = self.CURR_GRAPH_SIZE_THRESHOLD * 2 # Doubling the current graph size
						#print "Incrementing the solver graph size to " + str(self.CURR_GRAPH_SIZE_THRESHOLD)

				if rcGraphSat == False :
					# Apply non-Optimistic synthesis. 
					(rcGraphSat, synPaths) = self.enforceGraphPolicies(rcGraph=rcGraph, recovery=False)

				self.synthesisSuccessFlag = self.synthesisSuccessFlag & rcGraphSat
			self.enforceMulticastPolicies()		
		elif self.noOptimizationsFlag : 
			#st = time.time()
			self.synthesisSuccessFlag = self.enforceUnicastPoliciesNoOptimizations()
			#et = time.time()
			#print "No Optimizations time is", et - st
			self.enforceMulticastPolicies()		
		else : 
			self.synthesisSuccessFlag = self.enforceUnicastPolicies()
			self.enforceMulticastPolicies()		

		end_t = time.time()
		print "Time taken to solve the " + str(self.pdb.getPacketClassRange()) + " policies " + str(end_t - start_t)

		if self.synthesisSuccessFlag and self.OptimisticSynthesisFlag: 
			for pc in self.OptimisticPaths : 
				self.pdb.addPath(pc, self.OptimisticPaths[pc])
			self.pdb.validatePolicies(self.topology)
			#self.pdb.printPaths(self.topology)
		elif self.synthesisSuccessFlag and not self.OptimisticSynthesisFlag :
			self.pdb.validatePolicies(self.topology)
			#self.pdb.printPaths(self.topology)

		if self.controlPlaneMode : 
			dsts = self.pdb.getDestinations()
			for dst in dsts : 
				self.pdb.addDestinationDAG(dst, self.generateDestinationDAG(dst))

			self.zeppelinSynthesiser.enforceDAGs(self.pdb.getDestinationDAGs())
		

		self.pdb.validatePolicies(self.topology)
		#self.pdb.printPaths(self.topology)
		self.pdb.writeForwardingRulesToFile(self.topology)
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

		# Create Relational Packet Classses.
		relClasses = self.pdb.getRelationalClasses()

		# switchTableConstraints = self.pdb.getSwitchTableConstraints()
		# self.addSwitchTableConstraints(switchTableConstraints)  # Adding switch table constraints.

		if self.controlPlaneMode :
			print "In control plane generation mode"
			# Need to generate paths for synthesis of control plane
			for pc1 in range(self.pdb.getPacketClassRange()) : 
				for pc2 in range(pc1 + 1, self.pdb.getPacketClassRange()) :
					self.addDestinationTreeConstraints(pc1, pc2)

		linkCapacityConstraints = self.pdb.getLinkCapacityConstraints()
		self.addLinkConstraints(range(self.pdb.getPacketClassRange()), linkCapacityConstraints)

		if len(linkCapacityConstraints) > 0 :
			# Cannot synthesise relational Classes independently. 
			self.addTopologyConstraints(0, self.pdb.getPacketClassRange())

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
			solvetime = time.time()
			modelsat = self.z3Solver.check()
			self.z3solveTime += time.time() - solvetime
			if modelsat == z3.sat : 
				#print "Solver return SAT"
				self.fwdmodel = self.z3Solver.model()
				for pc in range(self.pdb.getPacketClassRange()) :
					self.pdb.addPath(pc, self.getPathFromModel(pc))		
			else :
				print "Input Policies not realisable"
		else : 			
			for relClass in relClasses :
				# Independent Synthesis of relClass.
				#self.z3Solver.push()
				#reachtime = time.time()

				for pc in relClass :
					if not self.pdb.isMulticast(pc):  
						policy = self.pdb.getReachabilityPolicy(pc)
						self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

						if not self.addGlobalTopoFlag : 
							#st = time.time()
							# Add Topology Constraints
							self.addTopologyConstraints(pc)

				#isolationtime = time.time()
				# Add traffic constraints. 
				for pno in range(self.pdb.getIsolationPolicyCount()) :
					pc = self.pdb.getIsolationPolicy(pno)
					pc1 = pc[0]
					pc2 = pc[1]
					if pc1 in relClass and pc2 in relClass: 
						self.addTrafficIsolationConstraints(pc1, pc2)
				
				#print "Time taken to add isolation constraints is", time.time() - isolationtime

				# Each relational class can be synthesised independently.
				solvetime = time.time()
				modelsat = self.z3Solver.check()
				self.z3solveTime += time.time() - solvetime
				#tprint "Time taken to solve constraints is " + str(time.time() - st)

				if modelsat == z3.sat : 
					#print "Solver return SAT"
					self.fwdmodel = self.z3Solver.model()
					for pc in relClass :
						self.pdb.addPath(pc, self.getPathFromModel(pc))
						
				else :
					print "Input Policies not realisable"
					unsatCores = self.z3Solver.unsat_core()
					for unsatCore in unsatCores :
						print str(unsatCore)

				#self.z3Solver.pop()

	def enforceUnicastPoliciesNoOptimizations(self) :
		""" Enforcement of Policies stored in the PDB. """

		self.addTopologyConstraints(0, self.pdb.getPacketClassRange())

		# switchTableConstraints = self.pdb.getSwitchTableConstraints()
		# self.addSwitchTableConstraints(switchTableConstraints)  # Adding switch table constraints.

		linkCapacityConstraints = self.pdb.getLinkCapacityConstraints()
		self.addLinkConstraints(range(self.pdb.getPacketClassRange()), linkCapacityConstraints)

		
		# Synthesize all together.
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


		#self.smtlib2file.write("(check-sat)\n")
		#self.smtlib2file.write("(get-model)\n")

		# Apply synthesis
		solvetime = time.time()
		modelsat = self.z3Solver.check()
		self.z3solveTime += time.time() - solvetime
		if modelsat == z3.sat : 
			#print "Solver return SAT"
			self.fwdmodel = self.z3Solver.model()
			for pc in range(self.pdb.getPacketClassRange()) :
				self.pdb.addPath(pc, self.getPathFromModel(pc))		
		else :
			print "Input Policies not realisable"

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
				#st = time.time()
				self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 
				#tprint "Time taken to add Reachability constraints is " + str(time.time() - st)
				
				if not self.addGlobalTopoFlag : 
					#st = time.time()
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

		#print "Starting Z3 check for " + str(pclist)
		st = time.time()
		solvetime = time.time()
		modelsat = self.z3Solver.check()
		self.z3solveTime += time.time() - solvetime
		if modelsat == z3.sat : 
			#tprint "Time taken to solve the constraints is " + str(time.time() - st)
			rcGraphSat = True
			#print "SAT"
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
		# Find mimimum cut of rcGraph
		st = time.time()
		edgecuts = nx.minimum_edge_cut(rcGraph)
		et = time.time() - st
		#print "MinCut time", et
		rcCopy = rcGraph.copy()
		rcCopy.remove_edges_from(edgecuts)
		smallest_cc = min(nx.connected_components(rcCopy), key=len)
		
		# If smallest_cc > 3, then a good minimum cut exists, otherwise, the minimum cut would simply return a set of 1 or 2 vertices.
		if len(smallest_cc) < self.MIN_GRAPH_THRESHOLD :
			# Use METIS equipartitioning.
			(edgecuts, partitions) = metis.part_graph(graph=rcGraph, nparts=2, contig=True) # Note : Metis overhead is minimal.

			# If the min-cut between the two partitions is greater than a threshold, dont partition. 
			no_attempts = 10

			random.seed(time.time())
			while edgecuts > self.CUT_THRESHOLD and no_attempts > 0:
				# try to partition into 4 and combining them with a random seed.
				#print "Attempting repartitions"
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
			
			OptimisticSolCount1 = 0
			OptimisticSolCount2 = 0

			rc1empty = True
			rc2empty = True
			i = 0

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
				#print "Cannot be partitioned"
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
		else :
			#print "Using min cut"
			# Use mincut itself. 
			graphs = list(nx.connected_component_subgraphs(rcCopy)) 	
			if len(graphs) <> 2 :
				#print "Cannot be partitioned"
				# Cannot partition the graph further. Apply synthesis. 
				(graphSat, synPaths) = self.enforceGraphPolicies(rcGraph,differentPathConstraints)
				return (graphSat, synPaths)

			rcGraph1 = graphs[0]
			rcGraph2 = graphs[1]

			OptimisticSolCount1 = 0
			OptimisticSolCount2 = 0

			for node in rcGraph1.nodes():
				pc = int(node)
				
				# Find Optimistic paths which are isolated to pc. 
				isolatedPcs = self.pdb.getIsolatedPolicies(pc)
				for ipc in isolatedPcs :
					if ipc in self.OptimisticPaths : 
						OptimisticSolCount1 += 1

			for node in rcGraph2.nodes():
				pc = int(node)
				
				# Find Optimistic paths which are isolated to pc. 
				isolatedPcs = self.pdb.getIsolatedPolicies(pc)
				for ipc in isolatedPcs :
					if ipc in self.OptimisticPaths : 
						OptimisticSolCount2 += 1

			# Decide on the order of RCgraph1 and RCgraph2. We must synthesize the graph which has more constraints 
			# and then the one with less constraints. 
			if OptimisticSolCount1 < OptimisticSolCount2 : 
				# Swap the order of graphs.
				rcGraph1, rcGraph2 = rcGraph2, rcGraph1


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
				pass
				#print "Program failed to find a solution"
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
		#print "Recovery Attempt #" + str(attempt) + " " + str(differentPathConstraints)
		if differentPathConstraints == None :
			localDifferentPathConstraints = []
		else : 
			localDifferentPathConstraints = list(differentPathConstraints)

		(rcGraph1Sat, synPaths1) = self.enforceGraphPoliciesOptimistic(rcGraph1, localDifferentPathConstraints)
			
		if rcGraph1Sat == False : 
			#print "Recovery Failed"
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

				solvetime = time.time()
				modelsat = self.z3Solver.check()
				self.z3solveTime += time.time() - solvetime
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


	def addTopologyConstraintsSAT(self, pcStart, pcEnd=0) :
		if pcEnd == 0 :
			""" Topology Constraint for one packet class"""
			pcEnd = pcStart + 1

		st = time.time()
		swCount = self.topology.getSwitchCount()
		# \forall sw \forall n \in neighbours(sw) and NextHop = {n | F(sw,n,pc,1) = True}. |NextHop| \leq 1 
		# None or only one of F(sw,n,pc,1) can be true.
		for pc in range(pcStart, pcEnd) :
			if not self.pdb.isMulticast(pc) :
				""" Unicast packet class """

				if not self.pdb.hasWaypoints(pc) :
					# Dont need to have topology forwarding constraints
					continue
				
				useBridgeSlicing = False
				if self.bridgeSlicingFlag :
					# Find if exists in a bridge slice. 
					srcSlice = self.topology.getBridgeSliceNumber(self.pdb.getSourceSwitch(pc))
					dstSlice = self.topology.getBridgeSliceNumber(self.pdb.getDestinationSwitch(pc))

					if srcSlice == dstSlice and srcSlice <> None : 
						# Path will exist only in this slice.
						swList = self.topology.getBridgeSlice(srcSlice)
						useBridgeSlicing = True
					else :
						swList = range(1,swCount + 1)
				else : 
					swList = range(1,swCount + 1)

				for sw in swList :
					neighbours = self.topology.getSwitchNeighbours(sw, useBridgeSlicing)

					# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
					topoAssertions = []
					unreachedAssertions = []
					
					unreachedAssertionsStr = ""
					topoAssertStr = ""

					for n in neighbours : 
						#neighbourAssert = self.F(sw,n,pc,1) == True
						neighbourAssertions = [self.Fwd(sw,n,pc)]
						unreachedAssertions.append(Not(self.Fwd(sw,n,pc)))

						neighbourAssertionsStr = self.FwdStr(sw,n,pc)
						unreachedAssertionsStr += " (not " + self.FwdStr(sw,n,pc) + ") "

						for n1 in neighbours :
							if n == n1 : 
								continue
							else :
								neighbourAssertions.append(Not(self.Fwd(sw,n1,pc)))

								neighbourAssertionsStr += " (not " + self.FwdStr(sw,n1,pc) + ") "
						
						neighbourAssert = And(*neighbourAssertions)
						topoAssertions.append(neighbourAssert)

						neighbourAssertStr = " (and " + neighbourAssertionsStr + ") "
						topoAssertStr += neighbourAssertStr

					unreachedAssert = And(*unreachedAssertions)
					topoAssertions.append(unreachedAssert) # Either one forwarding rule or no forwarding rules.
					topoAssert = Or(*topoAssertions) 

					unreachedAssertStr = " (and " + unreachedAssertionsStr + ") "
					topoAssertStr = " (or " + topoAssertStr + " " + unreachedAssertStr +  ") "
					#self.smtlib2file.write("; Forwarding Rule Constraint for switch " + str(sw) + "\n")
					#self.smtlib2file.write("( assert " + topoAssertStr + ")\n")

					self.z3numberofadds += 1
					#addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(topoAssert)
					#self.z3addTime += time.time() - addtime
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
							self.z3numberofadds += 1
							addtime = time.time() # Profiling z3 add.
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc), fwdSet(sw, pc, n) == 1))
							self.z3addTime += time.time() - addtime
							self.z3numberofadds += 1
							addtime = time.time() # Profiling z3 add.
							self.z3Solver.add(Implies(Not(self.Fwd(sw, n, pc)), fwdSet(sw, pc, n) == 0))
							self.z3addTime += time.time() - addtime
						else :
							prevn = neighbours[i - 1]
							self.z3numberofadds += 1
							addtime = time.time() # Profiling z3 add.
							self.z3Solver.add(Implies(self.Fwd(sw, n, pc), fwdSet(sw, pc, n) == 1 + fwdSet(sw, pc, prevn)))
							self.z3addTime += time.time() - addtime
							self.z3numberofadds += 1
							addtime = time.time() # Profiling z3 add.
							self.z3Solver.add(Implies(Not(self.Fwd(sw, n, pc)), fwdSet(sw, pc, n) == fwdSet(sw, pc, prevn)))
							self.z3addTime += time.time() - addtime
						i +=1
					n = neighbours[i - 1] # Last element in the list.
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(fwdSet(sw, pc, n) < 2)
					self.z3addTime += time.time() - addtime
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
						neighbourAssert = self.Fwd(sw,n,pc)
						unreachedAssert = And(unreachedAssert, Not(self.Fwd(sw,n,pc)))
						for n1 in neighbours :
							if n == n1 : 
								continue
							else :
								neighbourAssert = And(neighbourAssert, Not(self.Fwd(sw,n1,pc)))
						topoAssert = Or(topoAssert, neighbourAssert)

					topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(topoAssert)
					self.z3addTime += time.time() - addtime
				else :
					""" Multicast packet class. No restrictions on forwarding set """
					pass

	def addReachabilityConstraints(self, srcIP, srcSw, dstIP, dstSw, pc, W=None, pathlen=0) :
		#reachtime = time.time()
		if pathlen == 0 :
			# Default argument. Set to max.
			pathlen = self.topology.getMaxPathLength()
		
		# Add Reachability in atmost pathlen steps constraint. 
		#reachAssert = self.Reach(dstSw,pc,pathlen) == True

		reachAssertions = []
		reachAssertionsStr = ""
		for plen in range(1,pathlen+1) :
			reachAssertions.append(self.Reach(dstSw,pc,plen))

			reachAssertionsStr += self.ReachStr(dstSw,pc,plen) + " "

		reachAssert = Or(*reachAssertions)

		#self.smtlib2file.write("; Destination Reachability \n")
		#self.smtlib2file.write("(assert (or " + reachAssertionsStr + " ))\n")

		self.z3numberofadds += 1
		#addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(reachAssert)
		#self.z3addTime += time.time() - addtime

		# At Destination, forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(dstSw)
		
		destAssert = True
		destAssertStr = ""
		for n in neighbours :
			destAssert = And(destAssert, self.Fwd(dstSw,n,pc) == False)

			destAssertStr += " (not " + self.FwdStr(dstSw,n,pc) + " )"

		destAssertStr = "(and " + destAssertStr + ")"
		#self.smtlib2file.write("(assert " + destAssertStr + ")\n")

		self.z3numberofadds += 1
		#addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(destAssert)
		#self.z3addTime += time.time() - addtime

		
		if len(W) > 0 : 
			totalwaypointCount = 0
			currwaypointCount = 0
			for bags in W :
				totalwaypointCount += len(bags)

			prevbag = None
			for bags in W : 
				# ordered Waypoints.
				# Add the Waypoint Constraints. 
				currwaypointCount += len(bags)
				for w in bags :
					#self.smtlib2file.write("; Waypoint " + str(w) + " Reachability \n")			
						
					reachAssertions = []
					reachAssertionsStr = ""
					for plen in range(1 + currwaypointCount - len(bags), pathlen - (totalwaypointCount - currwaypointCount)) :
						reachAssertions.append(self.Reach(w,pc,plen))

						if prevbag <> None : 
							for w2 in prevbag : 
								orderAssertions = []
								for plen2 in range(1, plen): 
									orderAssertions.append(self.Reach(w2, pc, plen2))
								orderAssert = Implies(self.Reach(w, pc, plen), Or(*orderAssertions))
								self.z3Solver.add(orderAssert)
					
					reachAssert = Or(*reachAssertions)

					self.z3numberofadds += 1
					#addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(reachAssert)
					#self.z3addTime += time.time() - addtime
				prevbag = bags

				
		# # Weird Reach Constraint.
		# dstneighbours = self.topology.getSwitchNeighbours(dstSw)
		# # Only want one switch rule from neighbours of dst to dst. (thus ensuring a single path to destination)
		# singlePathAssertions = []
		# for n in dstneighbours : 
		# 	ruleAssertions = [self.Fwd(n, dstSw, pc)]
		# 	for n1 in dstneighbours :
		# 		if n <> n1 : 
		# 			ruleAssertions.append(Not(self.Fwd(n1, dstSw, pc)))
		# 	singlePathAssertions.append(And(*ruleAssertions))
		# self.z3Solver.add(Or(*singlePathAssertions))

		#st = time.time()
		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addTopologyTreeConstraints(srcSw, pc)
		self.addPathConstraints(srcSw,pc)		
		#et = time.time()
		#print "Path Constraints time is " + str(et - st)
		#print "total function takes ", time.time() - reachtime
		
	# Note This functions take the most time for each pc. Look for ways to improve this
	def addPathConstraints(self, s, pc) :
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()

		useBridgeSlicing = False
		if self.topologySlicingFlag : 
			swList = self.topology.getTopologySlice(self.topology.getSliceNumber(s))
		
		elif self.bridgeSlicingFlag :
			# Find if exists in a bridge slice. 
			srcSlice = self.topology.getBridgeSliceNumber(s)
			dstSlice = self.topology.getBridgeSliceNumber(self.pdb.getDestinationSwitch(pc))

			if srcSlice == dstSlice and srcSlice <> None : 
				# Path will exist only in this slice.
				swList = self.topology.getBridgeSlice(srcSlice)
				useBridgeSlicing = True
			else :
				swList = range(1,swCount + 1)
		else : 
			swList = range(1,swCount + 1)

		neighbours = self.topology.getSwitchNeighbours(s, useBridgeSlicing)
		
		srcAssertions = []
		srcAssertionsStr = ""
		for n in neighbours : 
			srcAssertions.append(And(self.Fwd(s,n,pc), self.Reach(n, pc, 1)))

			#srcAssertionsStr += " (and " + self.FwdStr(s,n,pc) + " " + self.ReachStr(n, pc, 1) + " )"

		self.z3numberofadds += 1
		#addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(Or(*srcAssertions))
		#self.z3addTime += time.time() - addtime

		#self.smtlib2file.write(";Source forwarding assertions \n")
		#self.smtlib2file.write("(assert (or" + srcAssertionsStr + "))\n")

		st = time.time()
		#constime = 0
		#addtime = 0
		for i in swList :
			if i == s : 
				continue

			#self.smtlib2file.write("; Backward Reachability Propagation for switch " + str(i) + "\n")

			for pathlen in range(1,maxPathLen+1) :
				if i not in self.bfsLists[pathlen] : 
					# Not at distance i in the topology tree, dont add constraints.
					continue 

				ineighbours = self.topology.getSwitchNeighbours(i, useBridgeSlicing) 
				if self.useTacticFlag and pc in self.tactics :
					# Use Tactic to reduce constraints.
					tactic = self.tactics[pc]
					labels = tactic.getPreviousLabels(self.topology.getLabel(i), pathlen)
					labelneighbours = []
					for n in ineighbours : 
						if self.topology.getLabel(n) in labels :
							labelneighbours.append(n)
					if len(labelneighbours) == 0 :
						# self.Reach(i,pc,pathlen) = False
						self.z3Solver.add(Not(self.Reach(i,pc,pathlen)))
						continue
					else :
						# Modify the ineighbours
						ineighbours = labelneighbours
				
				constraintKey = str(i) + ":" + str(pc) + "*" + str(pathlen)
				if constraintKey in self.backwardReachPropagationConstraints : 
					# Reuse constraint object if already created.
					backwardReachConstraint = self.backwardReachPropagationConstraints[constraintKey]
				else : 
					# Create constraint.
					beforeHopAssertions = []

					#beforeHopAssertionsStr = ""
					ct = time.time()
					for isw in ineighbours : 
						beforeHopAssertions.append(And(self.Fwd(isw, i, pc), self.Reach(isw, pc, pathlen - 1)))
						
					backwardReachConstraint = Implies(self.Reach(i,pc,pathlen), Or(*beforeHopAssertions))
					#constime += time.time() - ct

				#at = time.time()	
				self.z3Solver.add(backwardReachConstraint)
				#addtime += time.time() - at

				#beforeHopAssertStr = "(=> " + self.ReachStr(i,pc,pathlen) + " (or " + beforeHopAssertionsStr + " ))"
				#self.smtlib2file.write("(assert " + beforeHopAssertStr + " )\n")

				# Store constraint for reuse. 
				constraintKey = str(i) + ":" + str(pc) + "*" + str(pathlen)
				if constraintKey not in self.backwardReachPropagationConstraints :
					self.backwardReachPropagationConstraints[constraintKey] = backwardReachConstraint


		# print "constime", constime
		# print "addTime", addtimw
		# st = time.time()

	def addTopologyTreeConstraints(self, srcSw, pc) : 
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()

		swList = [srcSw]
		for k in range(1, maxPathLen + 1) :
			newSwList = []
			for sw in swList :
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours :
					if n not in newSwList : 
						newSwList.append(n)

			self.bfsLists[k] = newSwList
			# Set switches not in newSwList to false at Reach(k)
			for sw in range(1, swCount+1) :
				if sw not in newSwList  :
					self.z3Solver.add(Not(self.Reach(sw, pc, k)))

			swList = newSwList

	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """
		
		swCount = self.topology.getSwitchCount()
		useBridgeSlicing = False

		# Find bridges for pc1 and pc2.
		if self.bridgeSlicingFlag :
			# Find if exists in a bridge slice. 
			srcSlice1 = self.topology.getBridgeSliceNumber(self.pdb.getSourceSwitch(pc1))
			dstSlice1 = self.topology.getBridgeSliceNumber(self.pdb.getDestinationSwitch(pc1))
			srcSlice2 = self.topology.getBridgeSliceNumber(self.pdb.getSourceSwitch(pc2))
			dstSlice2 = self.topology.getBridgeSliceNumber(self.pdb.getDestinationSwitch(pc2))
			slice1 = None
			slice2 = None
			if srcSlice1 == dstSlice1 and srcSlice1 <> None :
				slice1 = srcSlice1
			if srcSlice2 == dstSlice2 and srcSlice2 <> None :
				slice2 = srcSlice2
			if slice1 <> None and slice2 <> None :
				# Both are in bridge slices.
				if slice1 <> slice2: 
					# pc1 and pc2 will be isolated naturally. 
					return
			if slice1 <> None or slice2 <> None : 
				# One of them is in a bridge slice. Only add traffic isolation constraints in that slice.
				if slice1 <> None : 
					slice = slice1
				else :
					slice = slice2
				swList = self.topology.getBridgeSlice(slice)
				useBridgeSlicing = True
			else :
				swList = range(1, swCount + 1) 
		else :
			swList = range(1, swCount + 1) 

		for sw in swList:
			#self.smtlib2file.write("; Traffic Isolation Constraints for switch " + str(sw) + "\n")
			for n in self.topology.getSwitchNeighbours(sw, useBridgeSlicing) :
				if self.weakIsolationFlag : 
					# Add constraints only for core, aggregate switch links. Using for evaluation
					# TODO : Policy interpreter.
					sw1 = self.topology.getSwName(sw)
					sw2 = self.topology.getSwName(n)
					if sw1[0] == "e" or sw2[0] == "e" :
						continue

				isolateAssert = Not( And (self.Fwd(sw,n,pc1), self.Fwd(sw,n,pc2)))
				self.z3numberofadds += 1
				#addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(isolateAssert)	
				#self.z3addTime += time.time() - addtime

				#self.smtlib2file.write("(assert (not (and " + self.FwdStr(sw,n,pc1) + " " + self.FwdStr(sw,n,pc2) + ")))\n")

	def addSliceTrafficIsolationConstraints(self, slice, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """

		swList = self.topology.getTopologySlice(slice)
		for sw in swList :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.Fwd(sw,n,pc1), self.Fwd(sw,n,pc2)))
				self.z3numberofadds += 1
				addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(isolateAssert)
				self.z3addTime += time.time() - addtime	

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
			diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc))

		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(Not(diffPathAssert))
		self.z3addTime += time.time() - addtime

	def addDifferentSolutionConstraint(self, pathConstraints) :
		""" Adding constraints such that the solution obtained is different from the solution provided by arg pathConstraints
			pathConstraints = List of [pc, path]"""
		diffPathAssert = True
		for pathConstraint in pathConstraints :
			i = 0
			pc = pathConstraint[0]
			path = pathConstraint[1]
			for i in range(len(path) - 1) :
				diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc))

		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(Not(diffPathAssert))
		self.z3addTime += time.time() - addtime

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
					diffPathAssert = And(diffPathAssert, self.Fwd(path[i], path[i+1], pc))

		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(Not(diffPathAssert))
		self.z3addTime += time.time() - addtime

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
		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(self.Fwd(sw1, sw2, pc) == False)
		self.z3addTime += time.time() - addtime

		# Add Link Capacity Constraints : 
		self.addLinkConstraints([pc], self.OptimisticLinkCapacityConstraints)

		successFlag = False
		solvetime = time.time()
		modelsat = self.z3Solver.check()
		self.z3solveTime += time.time() - solvetime
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
				reachAssert = self.F(srcSw,dstSw,pc,pathlen)
				self.z3numberofadds += 1
				addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(reachAssert)
				self.z3addTime += time.time() - addtime
		else :
			# Add Reachability in "exactly" pathlen steps constraint. 
			for dstSw in dstSwList : 
				reachAssert = self.F(srcSw,dstSw,pc,pathlen)
				reachAssert = And(reachAssert, self.F(srcSw,dstSw,pc,pathlen - 1) == False)
				self.z3numberofadds += 1
				addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(reachAssert)
				self.z3addTime += time.time() - addtime

		# At Destination, forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		for dstSw in dstSwList : 
			neighbours = self.topology.getSwitchNeighbours(dstSw)
		
			destAssert = True
			for n in neighbours :
				destAssert = And(destAssert, self.F(dstSw,n,pc,1) == False)

			self.z3numberofadds += 1
			addtime = time.time() # Profiling z3 add.
			self.z3Solver.add(destAssert)
			self.z3addTime += time.time() - addtime

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
					neighbourAssert = self.F(n,dst,pc,1)
					unreachedAssert = And(unreachedAssert, self.F(n,dst,pc,1) == False)
					for n1 in neighbours :
						if n == n1 : 
							continue
						else :
							neighbourAssert = And(neighbourAssert, self.F(n1,dst,pc,1) == False)
					singlePathAssert = Or(singlePathAssert, neighbourAssert)

				self.z3numberofadds += 1
				addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(Or(unreachedAssert, singlePathAssert))
				self.z3addTime += time.time() - addtime

		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addPathConstraints(srcSw,pc)	

		# Need to add cycle constraints as well!	
		fname = "rank" + str(pc)
		rankfn = Function(fname, IntSort(), IntSort())

		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(rankfn(srcSw) == 0)
		self.z3addTime += time.time() - addtime
		
		for i in range(1,self.topology.getSwitchCount() +1) :
			ineighbours = self.topology.getSwitchNeighbours(i) 

			for n in ineighbours :
				self.z3numberofadds += 1
				addtime = time.time() # Profiling z3 add.
				self.z3Solver.add(Implies(self.F(i,n,pc,1), rankfn(n) > rankfn(i)))
				self.z3addTime += time.time() - addtime

	def addBoundConstraints(self, pcRange) :
		self.z3numberofadds += 1
		addtime = time.time() # Profiling z3 add.
		self.z3Solver.add(self.pc < pcRange + 1)
		self.z3addTime += time.time() - addtime
	
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
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen), self.R(i, pc) == 1))
						self.z3addTime += time.time() - addtime
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == False, self.R(i, pc) == 0))
						self.z3addTime += time.time() - addtime
					else :
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(self.R(i, pc) == 0)
						self.z3addTime += time.time() - addtime
			else :
				for i in range(1,swCount+1) :
					if not i == dst :
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen), self.R(i, pc) == self.R(i, pc-1) + 1))
						self.z3addTime += time.time() - addtime
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(Implies(self.F(src, i, pc, maxPathLen) == False, self.R(i, pc) == self.R(i, pc-1)))
						self.z3addTime += time.time() - addtime
					else :
						self.z3numberofadds += 1
						addtime = time.time() # Profiling z3 add.
						self.z3Solver.add(self.R(i, pc) == self.R(i, pc-1))
						self.z3addTime += time.time() - addtime

		maxpc = self.pdb.getPacketClassRange() - 1
		for constraint in constraints :
			sw = constraint[0]
			self.z3numberofadds += 1
			addtime = time.time() # Profiling z3 add.
			self.z3Solver.add(self.R(sw, maxpc) < constraint[1] + 1)
			self.z3addTime += time.time() - addtime

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
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc), self.L(sw1, sw2, pc) == 1))
					self.z3addTime += time.time() - addtime
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == False, self.L(sw1, sw2, pc) == 0))
					self.z3addTime += time.time() - addtime
				else :
					prevpc = pclist[i - 1]
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc), self.L(sw1, sw2, pc) == self.L(sw1, sw2, prevpc) + 1))
					self.z3addTime += time.time() - addtime
					self.z3numberofadds += 1
					addtime = time.time() # Profiling z3 add.
					self.z3Solver.add(Implies(self.Fwd(sw1, sw2, pc) == False, self.L(sw1, sw2, pc) == self.L(sw1, sw2, prevpc)))
					self.z3addTime += time.time() - addtime
			i += 1

	def getPathFromModel(self, pc) :
		return self.getBFSModelPath(pc)

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

	def getBFSModelPath(self, pc):
		src = self.pdb.getSourceSwitch(pc)
		dst = self.pdb.getDestinationSwitch(pc)

		bfstree = dict()
		visited = dict()

		swQueue = deque([src])
		while len(swQueue) > 0 :
			sw = swQueue.popleft()
			visited[sw] = True
			if sw == dst :
				path = [dst]
				nextsw = bfstree[sw]
				while nextsw <> src :
					path.append(nextsw)
					nextsw = bfstree[nextsw]
				path.append(nextsw)
				# Reverse path.
				path.reverse()
				return path

			neighbours = self.topology.getSwitchNeighbours(sw)
			for n in neighbours : 
				if n not in visited and is_true(self.fwdmodel.evaluate(self.Fwd(sw,n,pc))) :
					bfstree[n] = sw
					swQueue.append(n)

		return []

	def enforceChangedPolicies(self):
		# A model already exists. Synthesis of newly added policies. 

		self.repairMode = True # Unicast constraints takes more time to solve. 

		self.z3Solver = Optimize()
		relClasses = self.pdb.getRelationalClasses()
		self.z3Solver.push()
		#create the updated relational Classes.
		for relClass in relClasses :
				# Independent Synthesis of relClass.
				#self.z3Solver.push()
				#reachtime = time.time()

			for pc in relClass :
				if not self.pdb.isMulticast(pc):  
					policy = self.pdb.getReachabilityPolicy(pc)
					self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1], pathlen=policy[2]) 

					if not self.addGlobalTopoFlag : 
						#st = time.time()
						# Add Topology Constraints
						self.addTopologyConstraints(pc)

			#isolationtime = time.time()
			# Add traffic constraints. 
			for pno in range(self.pdb.getIsolationPolicyCount()) :
				pc = self.pdb.getIsolationPolicy(pno)
				pc1 = pc[0]
				pc2 = pc[1]
				if pc1 in relClass and pc2 in relClass: 
					self.addTrafficIsolationConstraints(pc1, pc2)
			
			# Takes 3x more time than Solver() using Optimize()
			# solvetime = time.time()
			# modelsat = self.z3Solver.check()
			# print time.time() - solvetime, "Optimize Time taken for changed policies"
			# #print "Time taken to add isolation constraints is", time.time() - isolationtime

			#self.addMinRuleChangeConstraints(relClass)
			self.addMinSwitchChangeConstraints(relClass)

			# Each relational class can be synthesised independently.
			solvetime = time.time()
			modelsat = self.z3Solver.check()
			print time.time() - solvetime, "Time taken for changed policies"
			#self.z3solveTime += time.time() - solvetime
			#tprint "Time taken to solve constraints is " + str(time.time() - st)

			weight = 0
			if modelsat == z3.sat : 
				#print "Solver return SAT"
				self.fwdmodel = self.z3Solver.model()
				for pc in relClass :
					path = self.pdb.getPath(pc)
					for i in range(len(path) - 1) :
						if not is_true(self.fwdmodel.evaluate(self.Fwd(path[i], path[i+1], pc))) :
							weight += 1
					self.pdb.addPath(pc, self.getPathFromModel(pc))
				print weight
			else :
				print "Input Policies not realisable"

			#self.z3Solver.pop()

		#self.pdb.printPaths(self.topology)

	def addMinRuleChangeConstraints(self, relClass) : 
		# Add soft constraints for minimum rule change
		for pc in relClass :
			path = self.pdb.getPath(pc)
				
			for i in range(len(path) - 1) :
				#self.z3Solver.add_soft(arg=self.Reach(path[i+1], pc, i+1), id="rules")
				self.z3Solver.add_soft(arg=self.Fwd(path[i], path[i+1], pc), id="rules")

			# neighbours = self.topology.getSwitchNeighbours(path[i])
			# for n in neighbours :
			# 	self.z3Solver.add_soft(arg=Not(self.Fwd(path[i], n, pc)), id="rules")

			#self.z3Solver.add_soft(arg=self.Reach(path[len(path) - 1], pc, len(path) - 1), id="rules")

	def addMinSwitchChangeConstraints(self, relClass) :
		# Add soft constraints for minimum switch change
		swRuleMap = dict() # Rules of each switch
		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) : 
			swRuleMap[sw] = []
		for pc in relClass : 
			path = self.pdb.getPath(pc)

			for i in range(len(path) - 1) :
				swRuleMap[path[i]].append([path[i+1], pc])


		for sw in range(1, swCount + 1) :
			rules = swRuleMap[sw]
			swAssertions = []
			for r in rules : 
				swAssertions.append(self.Fwd(sw, r[0], r[1]))

			self.z3Solver.add_soft(arg=And(*swAssertions), id="switches")

		self.addMinRuleChangeConstraints(relClass)

		# disable switch with max rules
		maxrules = 0
		maxSw = None 
		for sw in swRuleMap.keys() :
			rules = swRuleMap[sw]
			if len(rules) > maxrules : 
				maxSw = sw
				maxrules = len(rules)

		neighbours = self.topology.getSwitchNeighbours(maxSw)
		for pc in relClass :
			for n in neighbours : 
				self.z3Solver.add(Not(self.Fwd(maxSw, n, pc)))



	# Profiling Statistics : 
	def printProfilingStats(self) :
		#print "Time taken to add constraints are ", self.z3addTime
		print "Genesis: Time taken to solve constraints are ", self.z3solveTime
		# print "Number of z3 adds to the solver are ", self.z3numberofadds

	def useTactic(self) :
		b1 = Blacklist("e .* e .* e", ["a","c","e"])
		b2 = Whitelist("e .* e",  ["a","c","e"])
		b3 = Blacklist("e . . . . . . . . . . .* e", ["a", "c", "e"])
		#b3 = Blacklist("e a c a c a c .* e", ["a", "c", "e"])

		self.topology.assignLabels()
		t = Tactic([b1, b2, b3], self.topology)

		st = time.time()
		t.findValidNeighbours(11)
		et = time.time()
		for pc in range(self.pdb.getPacketClassRange()) :
			if not self.pdb.hasWaypoints(pc) : 
				self.addTactic(t, pc)


	def addTactic(self, tactic, pc) :
		self.tactics[pc] = tactic
		
	def delta(self, state, label) :
		st = time.time()
		delta = self.currentTactic.getDelta()
		sink = self.currentTactic.getSinkState()
		deltaAssert = sink
		for transition in delta :
			deltaAssert = If(And(state == transition[0], label == transition[1]), transition[2], deltaAssert)

		print "delta time", time.time() - st
		return deltaAssert


	def addrhoConstraints(self, t, pc):
		""" t is the tactic """

		self.currentTactic = self.tactics[pc]

		dst = self.pdb.getDestinationSwitch(pc)
		src = self.pdb.getSourceSwitch(pc)
		q0 = t.getInitialState()
		
		initialStateAssert = self.rho(dst, pc) == self.delta(q0, t.getSwitchLabelMapping(dst))
		self.z3Solver.add(initialStateAssert)

		swCount = self.topology.getSwitchCount()
		swList = range(1,swCount+1)
		maxPathLen = self.topology.getMaxPathLength()

		sink = t.getSinkState()
		if sink == -1 : 
			print "No sink." 
			exit(0)
		st = time.time()

		for i in swList :
			# Add non-sink constraints.
			self.z3Solver.add(Not(self.rho(i,pc) == sink)) 

			ineighbours = self.topology.getSwitchNeighbours(i) 

			for isw in ineighbours : 
				ct = time.time()
				tacticAssert = Implies(self.Fwd(i, isw, pc), self.rho(i, pc) == self.delta(self.rho(isw, pc), t.getSwitchLabelMapping(i)))
				self.z3Solver.add(tacticAssert)
					
			
		print "Tactic constraints time is " + str(time.time() - st)
	
	def addDestinationTreeConstraints(self, pc1, pc2) : 
		""" If pc1 and pc2 have the same destination, then
		the paths must not form a cycle. """ 
		dst1 = self.pdb.getDestinationSwitch(pc1)
		dst2 = self.pdb.getDestinationSwitch(pc2)
		if dst1 <> dst2 : 
			return 

		# If pc1 and pc2 intersect (are reachable at a switch), 
		# then both are forwarded to the same switch. 
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()

		print "adding for ", pc1, pc2
		for sw in range(1, swCount + 1):
			if sw == dst1 : continue
			reachAssertions1 = []
			reachAssertions2 = []
			neighbours = self.topology.getSwitchNeighbours(sw)
			for plen in range(1, maxPathLen + 1):
				reachAssertions1.append(self.Reach(sw, pc1, plen))
				reachAssertions2.append(self.Reach(sw, pc2, plen))

			nextSwAssertions = []
			for n in neighbours : 
				nextSwAssertions.append(And(self.Fwd(sw, n, pc1), self.Fwd(sw, n, pc1)))

			# if a switch is reachable by pc1 and pc2, next switch in the path has to be the same.
			self.z3Solver.add(Implies(And(Or(*reachAssertions1), Or(*reachAssertions2)), Or(*nextSwAssertions)))


	def generateDestinationDAG(self, dst) :
		""" Create a spanning tree from all sources to destination  
		with already enforced policies """ 

		pcs = []
		for pc in range(self.pdb.getPacketClassRange()) :
			if dst == self.pdb.getDestinationSwitch(pc) : 
				pcs.append(pc)

		if len(pcs) == 0 :
			return

		swCount = self.topology.getSwitchCount()

		inDag = dict()
		dag = dict() # For every node, we will have a single successor.

		dag[dst] = None
		dag[dst] = True
		for sw in range(1, swCount + 1) :
			inDag[sw] = False

		for pc in pcs : 
			path = self.pdb.getPath(pc)
			for i in range(len(path) - 1) :
				sw1 = path[i]
				sw2 = path[i+1]
				inDag[sw1] = True
				dag[sw1] = sw2

		# Perform BFS from dst to include all switches in the DAG.
		swQueue1 = [dst]
		swQueue2 = []

		while len(swQueue1) > 0 :
			for sw in swQueue1 : 
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours : 
					if not inDag[n] : 
						inDag[n] = True
						dag[n] = sw
						if n not in swQueue2 : 
							swQueue2.append(n)
			swQueue1 = swQueue2 
			swQueue2 = []
		
		assert(len(dag) == swCount)


def toSMT2Benchmark(f, status="unknown", name="benchmark", logic=""):
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