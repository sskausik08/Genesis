from z3 import *
from Topology import Topology
import time
import random

class ConstraintGenerator2(object) :
	def __init__(self, topo) :
		self.topology = topo

		# Network Forwarding Function
		self.F = Function('F', IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())
		self.N = Function('N', IntSort(), IntSort(), BoolSort())
		self.pc = Int('pc') # Generic variable for packet classes
		self.z3Solver = Solver()
		self.fwdmodel = None 
		self.pcRange = 5

		# Add Common Constraints 
		self.addBoundConstraints(self.pcRange)
		self.addTopologyConstraints()

	def generateAssertions(self) :	

		start_t = time.time()
		print "Adding Constraints at " + str(start_t)
	
		for i in range(3, self.topology.getMaxPathLength() + 1) :
			self.z3Solver.push()
			self.addFinalReachabilityConstraints(1,3,1,i)
			self.addWaypointConstraints(1,3,1,[4,5])
			sat = self.z3Solver.check()
			if sat == z3.sat : 
				print "Sat " + str(i)
				break
			else :
				print "unsat " + str(i)
				self.z3Solver.pop()

		# for i in range(1, self.topology.getMaxPathLength() + 1) :
		# 	self.z3Solver.push()
		# 	self.addFinalReachabilityConstraints(1,2,2,i)
		# 	self.addWaypointConstraints(1,2,2,[4])
		# 	sat = self.z3Solver.check()
		# 	if sat == z3.sat : 
		# 		print "2Sat " + str(i)
		# 		break
		# 	else :
		# 		print "2unsat " + str(i)
		# 		self.z3Solver.pop()

		# print self.z3Solver.model()


		# self.addReachabilityConstraints(1,3,3)
		# self.addWaypointConstraints(1,3,3,[4])

		# self.addReachabilityConstraints(1,3,4)

		# self.addReachabilityConstraints(1,3,5)

		# self.addTrafficIsolationConstraints(4,5)
		# self.addTrafficIsolationConstraints(3,5)
		# self.addTrafficIsolationConstraints(4,3)


		
	
		# for i in range(1,10):
		# 	if i % 2 == 0 :
		# 		s = 1
		# 	else :
		# 		s = 2

		# 	d = random.randint(8,10)
		# 	self.addFinalReachabilityConstraints(s,d,i,self.topology.getMaxPathLength())
		# 	self.addWaypointConstraints(s,d,i, [random.randint(3,5), random.randint(6,7)])

		# 	if(i > 2) :
		# 		self.addTrafficIsolationConstraints(i, i - 1)


		#self.z3Solver.check()
		self.fwdmodel = self.z3Solver.model()
		print self.fwdmodel


		end_t = time.time()
		print "Time taken to solve the constraints is" + str(end_t - start_t)
		print self.getPath(1,1)


	def addTopologyConstraints(self) :
		swCount = self.topology.getSwitchCount()
		# \forall sw \forall n \in neighbours(sw) and NextHop = {n | F(sw,n,pc,1) = True}. |NextHop| \leq 1 
		# None or only one of F(sw,n,pc,1) can be true.
		for sw in range(1,swCount+1) :
			neighbours = self.topology.getSwitchNeighbours(sw)

			# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
			topoAssert = False
			unreachedAssert = True

			for n in neighbours : 
				neighbourAssert = self.F(sw,n,self.pc,1) == True
				unreachedAssert = And(unreachedAssert, self.F(sw,n,self.pc,1) == False)
				for n1 in neighbours :
					if n == n1 : 
						continue
					else :
						neighbourAssert = And(neighbourAssert, self.F(sw,n1,self.pc,1) == False)
				topoAssert = Or(topoAssert, neighbourAssert)

			topoAssert = Or(topoAssert, unreachedAssert) # Either one forwarding rule or no forwarding rules.
			topoAssert = ForAll(self.pc, topoAssert)
			self.z3Solver.add(topoAssert)
			
			# \forall n such that n \notin neighbours or n \not\eq sw . F(sw,n,pc,1) = False
			# Cannot reach nodes which are not neighbours in step 1. 
			# This constraint is needed because there is no restriction from the above constraints 
			# regarding the values of non-neighbours.
			for s in range(1,swCount + 1) :
				if s == sw or s in neighbours : 
					continue
				else :
					self.z3Solver.add(ForAll(self.pc, self.F(sw,s,self.pc,1) == False))

	def addNeighbourConstraints(self) :
		swCount = self.topology.getSwitchCount()
		for sw in range(0,swCount) :
			neighbours = self.topology.getSwitchNeighbours(sw)

			for i in range(swCount+1) : 
				if i in neighbours : 
					self.z3Solver.add(self.N(sw,i) == True)
				else :
					self.z3Solver.add(self.N(sw,i) == False)

	def addFinalReachabilityConstraints(self, s, d, pc, pathlen, isDest=True) :

		# Add topology constraint for this packet class :
		#self.addTopologyConstraints(pc)
		reachAssert = self.F(s,d,pc,pathlen) == True

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(d)

		if isDest : 
			destAssert = True
			for n in neighbours :
				destAssert = And(destAssert, self.F(d,n,pc,1) == False)

			self.z3Solver.add(destAssert)

		# Add Path Constraints
		self.addPathConstraints(s,pc)

	def addWaypointConstraints(self, s, d, pc, W) :
		maxPathLen = self.topology.getMaxPathLength()
		for w in W :
			reachAssert = self.F(s,w,pc,maxPathLen) == True
			self.z3Solver.add(reachAssert)
			

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
		# Isolation of traffic for packet classes pc1 and pc2. 
		swCount = self.topology.getSwitchCount()

		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.F(sw,n,pc1,1) == True, self.F(sw,n,pc2,1) == True))
				self.z3Solver.add(isolateAssert)		


	def addBoundConstraints(self, pcRange) :
		self.z3Solver.add(self.pc < pcRange + 1)

	def getPath(self, s, pc) :
		path = [s]
		swCount = self.topology.getSwitchCount()
		
		for sw in range(1, swCount + 1) :
			if sw == s : 
				continue
			if is_true(self.fwdmodel.evaluate(self.F(s,sw,pc,1))) :
				path.extend(self.getPath(sw,pc))
				return path
		
		return path
		
	def validateIsolation(self, pc1, pc2) :
		""" Validation of packet classes pc1 and pc2 are isolated."""

		path1 = self.getPath(pc1,)


"""Policy Database is used to maintain the database of policies incorporated in the network. 
This will help in better bookmarking and aid in policy change synthesis."""
class policyDatabase(object) :
	def __init__(self) :
		self.pc = 0
		self.endpointTable = []
		self.waypointTable = []
		self.IsolationTable = []

	def addAllowPolicy(self, srcIP, srcSw, dstIP, dstSw, W=None) :
		""" srcSw = source IP next hop switch
			dstSw = Destination IP next hop switch
			W = List of Waypoints. """

		self.endpointTable.append([srcIP, dstIP, srcSw, dstSw])
		if W == None : 
			self.waypointTable.append([])

		self.pc += 1
		return self.pc - 1


	def addIsolationPolicy(self, srcIP1, dstIP1, srcIP2, dstIP2) :
		# Find the Packet Class numbers
		i = 0
		pc1 = -1
		pc2 = -1
		for ep in endpointTable :
			if ep[0] == srcIP1 and ep[1] == dstIP1 :
				pc1 = i 
			if ep[0] == srcIP2 and ep[1] == dstIP2 :
				pc2 = i
			i += 1	

		if pc1 == -1 :
			#Flows dont exist. 
			raise LookupError(srcIP1 + "->" + dstIP1 + " is not a valid packet class flow.")
		elif pc2 == -1 :
			raise LookupError(srcIP1 + "->" + dstIP2 + " is not a valid packet class flow.")
		else : 
			self.IsolationTable.append([pc1,pc2])


t = Topology()
c = ConstraintGenerator2(t)
c.generateAssertions()
