from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx
from NetworkPredicate import *


class SliceGraphSolver(object) :
	def __init__(self) :
		self.topology = Topology(name="sliceGraph")

		# Network Forwarding Function
		#self.Fwd = Function('Fwd', IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())
		#self.Reach = Function('Reach', IntSort(), IntSort(), IntSort(), BoolSort())

		self.R = Function('R', IntSort(), IntSort(), IntSort())
		self.L = Function('L', IntSort(), IntSort(), IntSort(), IntSort())
		self.pc = Int('pc') # Generic variable for packet classes
		
		self.z3Solver = Solver()
		self.z3Solver.set(unsat_core=True)
		self.fwdmodel = None 

		# Policy Database. 
		self.pdb = PolicyDatabase()

		# Store edge nodes mappings
		self.edgeNodes = []
		self.sliceNodes = []
		
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

	def initializeSATVariables(self) :
		swCount = self.topology.getSwitchCount()
		pcRange = self.pdb.getPacketClassRange()
		maxPathLen = self.topology.getMaxPathLength()

		self.fwdvars = [[[[0 for x in range(pcRange)] for x in range(swCount + 1)] for x in range(swCount + 1)] for x in range(swCount + 1)]
		self.reachvars = [[[0 for x in range(maxPathLen+1)] for x in range(pcRange)] for x in range(swCount + 1)]

		for sw0 in range(1,swCount+1) : 
			for sw1 in range(1,swCount+1):
				for sw2 in range(1,swCount+1):
					for pc in range(pcRange) :
						self.fwdvars[sw0][sw1][sw2][pc] = Bool(str(sw0)+"-"+str(sw1)+"-"+str(sw2)+":"+str(pc))

		for sw in range(1,swCount+1):
			for pc in range(pcRange) :
				for plen in range(0,maxPathLen +1) :
					self.reachvars[sw][pc][plen] = Bool(str(sw)+":"+str(pc)+":"+str(plen))

	def Fwd(self, sw0, sw1, sw2, pc) :
		neighbours = self.topology.getSwitchNeighbours(sw1)
		if sw2 not in neighbours: 
			return False
		if sw0 not in neighbours and sw0 <> self.pdb.getSourceSwitch(pc) :
			return False
		else : 
			return self.fwdvars[sw0][sw1][sw2][pc]

	def Reach(self, sw, pc, plen) :
		if plen == 0 : 
			src = self.pdb.getSourceSwitch(pc)
			if sw == src : 
				return True
			else : 
				return self.Fwd(src,src,sw,pc)
		return self.reachvars[sw][pc][plen]

	def addSliceNode(self, sw, edges) : 
		""" Edges is a list of slice edgeKeys """
		
		self.topology.addSwitch(str(sw), edges)
		for edge in edges : 
			eID = self.topology.getSwID(edge) 
			if eID not in self.edgeNodes : 
				self.edgeNodes.append(eID)

		swID = self.topology.getSwID(str(sw))
		if swID not in self.sliceNodes : 
			self.sliceNodes.append(swID)

	def enforcePolicies(self): 
		self.initializeSATVariables()

		start_t = time.time()

		self.topology.printSwitchMappings()
		# Add Unreachable Constraints 
		st = time.time()
		 
		print "Unreachable Hop Constraints take ", time.time() - st

		st = time.time()
		self.addTopologyConstraints(0, self.pdb.getPacketClassRange())
		#tprint "Time to add global topology constraints", time.time() - st
	
		self.synthesisSuccessFlag = self.enforceUnicastPolicies()		

		if self.synthesisSuccessFlag : 
			#self.pdb.validatePolicies()
			self.pdb.printPaths(self.topology)

		end_t = time.time()
		print "Time taken to solve the policies with Optimistic flag is " + str(end_t - start_t)
	

	def addReachabilityPolicy(self, src, dst, waypoints=None) :
		""" src = next hop switch of source host(s) 
			dst = next hop switch of destination host(s)
			W = Waypoint Set (list of nodes) """

		# Translate s, d, W into logical topology numbers.
		srcSw = self.topology.getSwID(str(src))
		dstSw = self.topology.getSwID(str(dst))
		W = None
		if not waypoints == None :
			W = []
			for w in waypoints :
				W.append(self.topology.getSwID(str(w)))

		# Add policy to PDB : 
		pc = self.pdb.addReachabilityPolicy(TrueNP(), srcSw, dstSw, W)
		return pc

	def addTrafficIsolationPolicy(self, policy1, policy2) : 
		# Isolation of traffic for Policies policy1 and policy2
		pc = self.pdb.addIsolationPolicy(policy1,policy2) 

	def enforceUnicastPolicies(self) :
		""" Enforcement of Policies stored in the PDB. """
		self.topology.setMaxPathLength(5)

		# Cannot synthesise relational Classes independently. 
		for pc in range(self.pdb.getPacketClassRange()) :
			if not self.pdb.isMulticast(pc) : 
				policy = self.pdb.getReachabilityPolicy(pc)
				self.addReachabilityConstraints(srcIP=policy[0][0], srcSw=policy[0][2], dstIP=policy[0][1], dstSw=policy[0][3],pc=pc, W=policy[1]) 

		# Add traffic constraints. 
		for pno in range(self.pdb.getIsolationPolicyCount()) :
			pcs = self.pdb.getIsolationPolicy(pno)
			pc1 = pcs[0]
			pc2 = pcs[1]
			self.addTrafficIsolationConstraints(pc1, pc2)
		
		policiesSat = False
		# Apply synthesis
		modelsat = self.z3Solver.check()
		if modelsat == z3.sat : 
			policiesSat = True
			print "Solver return SAT"
			self.fwdmodel = self.z3Solver.model()
			print self.fwdmodel
			for pc in range(self.pdb.getPacketClassRange()) :
				self.pdb.addPath(pc, self.getPathFromModel(pc))		
		else :
			print "Input Policies not realisable"
			policiesSat = False

		return policiesSat

	# def addUnreachableHopConstraints(self) :
	# 	swCount = self.topology.getSwitchCount()
	# 	for sw in range(1,swCount+1) :
	# 		# \forall n such that n \notin neighbours or n \not\eq sw . F(sw,n,pc,1) = False
	# 		# Cannot reach nodes which are not neighbours in step 1. 
	# 		# This constraint is needed because there is no restriction from the above constraints 
	# 		# regarding the values of non-neighbours.
	# 		neighbours = self.topology.getSwitchNeighbours(sw)
	# 		for s in range(1,swCount + 1) :
	# 			if s == sw or s in neighbours : 
	# 				continue
	# 			else :
	# 				for n in neighbours : 
	# 					self.z3Solver.add(ForAll(self.pc, self.Fwd(n,sw,s,self.pc) == False))
	# 					self.z3Solver.add(ForAll(self.pc, self.Fwd(s,sw,n,self.pc) == False))
	# 				for s1 in range(1, swCount+1) :
	# 					if s1 == sw or s1 in neighbours : 
	# 						continue
	# 					else :
	# 						self.z3Solver.add(ForAll(self.pc, self.Fwd(s1,sw,s,self.pc) == False))
	# 						self.z3Solver.add(ForAll(self.pc, self.Fwd(s,sw,s1,self.pc) == False))


	def addTopologyConstraints(self, pcStart, pcEnd=0) :
		if pcEnd == 0 :
			""" Topology Constraint for one packet class"""
			pcEnd = pcStart + 1

		swCount = self.topology.getSwitchCount()
		# \forall sw \forall n \in neighbours(sw) and NextHop = {n | F(sw,n,pc,1) = True}. |NextHop| \leq 1 
		# None or only one of F(sw,n,pc,1) can be true.
		for pc in range(pcStart, pcEnd) :
			for sw in range(1,swCount+1) :
				if sw in self.sliceNodes : 
					""" Slice node. """
					neighbours = self.topology.getSwitchNeighbours(sw)

					for prev in neighbours : 
						# Add assertions to ensure f(prev, sw,*) leads to a valid neighbour. 
						topoAssert = False
						unreachedAssert = True

						for n in neighbours : 
							if prev == n : 
								self.z3Solver.add(self.Fwd(prev, sw, prev, pc) == False)
							neighbourAssert = self.Fwd(prev,sw,n,pc) == True
							unreachedAssert = And(unreachedAssert, self.Fwd(prev,sw,n,pc) == False)
							for n1 in neighbours :
								if n == n1 : 
									continue
								else :
									neighbourAssert = And(neighbourAssert, self.Fwd(prev,sw,n1,pc) == False)
							topoAssert = Or(topoAssert, neighbourAssert)

						topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
						self.z3Solver.add(topoAssert)


	def addReachabilityConstraints(self, srcIP, srcSw, dstIP, dstSw, pc, W=None, pathlen=0) :
		if pathlen == 0 :
			# Default argument. Set to max.
			pathlen = self.topology.getMaxPathLength()
		
		# Add Reachability in atmost pathlen steps constraint. 
		reachAssert = False
		for plen in range(pathlen) : 
			reachAssert = Or(reachAssert, self.Reach(dstSw,pc,plen) == True)
		self.z3Solver.add(reachAssert)

		if not W == None : 
			print W
			# Add the Waypoint Constraints. 
			for w in W :
				waypointAssert = False
				for plen in range(pathlen) : 
					waypointAssert = Or(waypointAssert, self.Reach(w,pc,plen))
				self.z3Solver.add(waypointAssert)
				

		st = time.time()
		# Add Path Constraints for this flow to find the forwarding model for this flow.
		self.addPathConstraints(srcSw,pc)		
		et = time.time()
		#tprint "Path Constraints time is " + str(et - st)
		

	# Note This functions take the most time for each pc. Look for ways to improve this
	def addPathConstraints(self, s, pc) :
		maxPathLen = self.topology.getMaxPathLength()
		
		neighbours = self.topology.getSwitchNeighbours(s)

		# Ensuring one rule from the start.
		sourceAssert = False
		for n in neighbours : 
			nn = self.topology.getSwitchNeighbours(n)
			for n2 in nn :
				if n2 <> s : 
					nextsw = n2
			neighbourAssert = And(self.Fwd(s,s,n,pc), self.Reach(s,pc,0), self.Reach(n,pc,0), self.Fwd(s,n,nextsw,pc), self.Reach(nextsw, pc, 1))
			for n1 in neighbours :
				if n == n1 : 
					continue
				else :
					neighbourAssert = And(neighbourAssert, self.Fwd(s,s,n1,pc) == False)
			sourceAssert = Or(sourceAssert, neighbourAssert)

		self.z3Solver.add(sourceAssert)
		
		#tprint "Path1 " + str(time.time() - st)
		st = time.time()

		for i in self.sliceNodes :
			ineighbours = self.topology.getSwitchNeighbours(i) 

			for nextsw in ineighbours : 
				for prevsw in ineighbours : 
					for plen in range(2,maxPathLen+1) :
						nextswn = self.topology.getSwitchNeighbours(nextsw)
						for n in nextswn : 
							if n <> i : 
								nextswnext = n

						nextHopAssert = Implies(And(self.Reach(prevsw,pc,plen-1), self.Reach(i,pc,plen), self.Fwd(prevsw, i, nextsw, pc)), And( Not(prevsw == nextsw), self.Reach(nextsw,pc,plen), self.Fwd(i,nextsw,nextswnext, pc), self.Reach(nextswnext, pc, plen + 1)))
						self.z3Solver.add(nextHopAssert)

						
		
		for i in self.sliceNodes :
			ineighbours = self.topology.getSwitchNeighbours(i) 

			for nextsw in ineighbours : 
				for prevsw in ineighbours : 
					for plen in range(1,maxPathLen+1) :
						nextswn = self.topology.getSwitchNeighbours(nextsw)
						for n in nextswn : 
							if n <> i : 
								nextswnext = n
						
						# If Reach, forwarding rule on slicenode must exist. 
						ruleAssert = Implies(And(self.Reach(prevsw,pc,plen-1), self.Reach(i,pc,plen), self.Reach(nextsw,pc,plen)), self.Fwd(prevsw, i, nextsw, pc))
						self.z3Solver.add(ruleAssert)

		#tprint "Path2 " + str(time.time() - st)
		st = time.time()

		for i in self.sliceNodes :
			ineighbours = self.topology.getSwitchNeighbours(i) 
	
			for plen in range(2,maxPathLen+1) :
				beforeHopAssert = False
				for prevsw in ineighbours : 
					prevn = self.topology.getSwitchNeighbours(prevsw)
					for p in prevn : 
						if p <> i : 
							prevswprev = p

					beforeHopAssert = Or(beforeHopAssert, And(self.Reach(prevsw, pc, plen - 1), self.Reach(prevswprev, pc, plen - 1), self.Fwd(prevswprev, prevsw, i, pc)))
				
				pathAssert = Implies(self.Reach(i,pc,plen), beforeHopAssert)
				self.z3Solver.add(pathAssert)

		# Add rules ensuring Reach for plen is true only for one sliceNode. 
		for plen in range(maxPathLen+1) : 
			for i in self.sliceNodes : 
				reachAssert = True
				for j in self.sliceNodes : 
					if i <> j : 
						reachAssert = And(reachAssert, Not(self.Reach(j, pc, plen)))
				self.z3Solver.add(Implies(self.Reach(i,pc,plen), reachAssert))


		# for i in swList :
		# 	if i == s : 
		# 		continue

		# 	# if Fwd rule exists, node should be reachable.
		# 	ineighbours = self.topology.getSwitchNeighbours(i)

		# 	for isw in ineighbours :
		# 		self.z3Solver.add(Implies(self.Fwd(i,isw,pc), self.Reach(i,pc,maxPathLen)))

		#tprint "Path3 " + str(time.time() - st)
		st = time.time()

	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		""" Adding constraints for Isolation Policy enforcement of traffic for packet classes (end-points) ep1 and ep2. """

		swCount = self.topology.getSwitchCount()
		for sw in self.edgeNodes :
			neighbours = self.topology.getSwitchNeighbours(sw)
			if len(neighbours) <> 2 :
				print "FRhivjgnkbvnkdgnl"
				exit(0)
			self.z3Solver.add(Not( And (self.Fwd(neighbours[0], sw, neighbours[1],pc1), self.Fwd(neighbours[0], sw, neighbours[1], pc2))))
			self.z3Solver.add(Not( And (self.Fwd(neighbours[1], sw, neighbours[0],pc1), self.Fwd(neighbours[1], sw, neighbours[0], pc2))))		

	def getPathFromModel(self, pc) :
		def getPathHelper(prev, curr, pc) :
			path = [curr]
			swCount = self.topology.getSwitchCount()
			neighbours = self.topology.getSwitchNeighbours(curr)
			for sw in neighbours :
				if is_true(self.fwdmodel.evaluate(self.Fwd(prev,curr,sw,pc))) :
					path.extend(getPathHelper(curr,sw,pc))
					return path
			
			return path

		src = self.pdb.getSourceSwitch(pc) 
		return getPathHelper(src, src, pc)

	def push(self) :
		self.z3Solver.push()

	def pop(self) :
		self.z3Solver.pop()  

s = SliceGraphSolver()
s.addSliceNode(1, ["a", "b", "c", "d"])
s.addSliceNode(2, ["a", "b"])
s.addSliceNode(3, ["c", "d"])
pc1 = s.addReachabilityPolicy(1, 3, [2])
pc2 = s.addReachabilityPolicy(1, 3)
s.addTrafficIsolationPolicy(pc1, pc2)
s.enforcePolicies()















# nuZ3
# maxSAT
# US Backbone, RocketFuelS