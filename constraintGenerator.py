from z3 import *
from Topology import Topology
import time
import random

class ConstraintGenerator(object) :
	def __init__(self, topo) :
		self.topology = topo

		# Network Forwarding Function
		self.F = Function('F', IntSort(), IntSort(), IntSort())
		self.x = Int('x')  # Generic variable for nodes.
		self.pc = Int('pc') # Generic variable for packet classes
		self.z3Solver = Solver()

	def generateAssertions(self) :	

		start_t = time.time()
		print "Adding Constraints at " + str(start_t)

		# self.addReachabilityConstraints(1,2,1)
		# self.addWaypointConstraints(1,2,1,[5])

		# self.addReachabilityConstraints(1,2,2)

		# self.addReachabilityConstraints(1,3,3)
		# self.addWaypointConstraints(1,3,3,[5])

		# self.addReachabilityConstraints(1,3,4)

		# self.addReachabilityConstraints(1,3,5)

		# self.addTrafficIsolationConstraints(4,5)
		# self.addTrafficIsolationConstraints(3,5)
		# self.addTrafficIsolationConstraints(4,3)


		# Add Bound Constraints on x and pc.
		self.addBoundConstraints(self.topology.getSwitchCount() - 1, 5)
		self.addTopologyConstraints()
	
		for i in range(1,10):
			if i % 2 == 0 :
				s = 1
			else :
				s = 2

			d = random.randint(3,10)
			self.addReachabilityConstraints(s,d,i)
			self.addWaypointConstraints(s,d,i, [random.randint(3,6), random.randint(7,10)])


		end_t = time.time()
		print "Time taken to add the constraints is" + str(end_t - start_t)

		start_t = time.time()
		print "Starting Solver at " + str(start_t)
		print self.z3Solver.check()
		print self.z3Solver.model()
		end_t = time.time()
		print "Time taken to find the network forwarding function is " + str(end_t - start_t)


	# Returns F^n(x)
	def composeF(self, n, x, pc) :
		cf = x
		for i in range(n) :
			cf = self.F(cf,pc)
		return cf

	def addTopologyConstraints(self) :
		swCount = self.topology.getSwitchCount()

		for sw in range(swCount) :
			neighbours = self.topology.getSwitchNeighbours(sw)

			# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
			topoAssert = self.F(sw,self.pc) == sw   # Can self loop to itself.

			for n in neighbours : 
				topoAssert = Or(topoAssert, self.F(sw,self.pc) == n)
			
			topoAssert = ForAll(self.pc, topoAssert)
			self.z3Solver.add(topoAssert)

	def addIntermediateReachabilityConstraints(self, s, d, pc, isDest=True) :
		# Add topology constraint for this packet class :
		#self.addTopologyConstraints(pc)

		maxPathLen = self.topology.getMaxPathLength()
		reachAssert = False

		for i in range(1,maxPathLen + 1) :
			reachAssert = Or(reachAssert, self.composeF(i,s,pc) == d)

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,pc) must be d. 
		# When we perform the translation to rules, we can forward it to host accordingly.

		if isDest :
			destAssert = (self.F(d,pc) == d)
			self.z3Solver.add(destAssert)

	def addReachabilityConstraints(self, s, d, pc, isDest=True) :
		# Add topology constraint for this packet class :
		#self.addTopologyConstraints(pc)

		maxPathLen = self.topology.getMaxPathLength()
		reachAssert = self.composeF(maxPathLen,s,pc) == d

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,pc) must be d. 
		# When we perform the translation to rules, we can forward it to host accordingly.

		if isDest :
			destAssert = (self.F(d,pc) == d)
			self.z3Solver.add(destAssert)


	def addWaypointConstraints(self, s, d, pc, W) :
		for w in W :
			self.addIntermediateReachabilityConstraints(s, w, pc, False)

	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		# Isolation of traffic for packet classes pc1 and pc2. 
		swCount = self.topology.getSwitchCount()

		for sw in range(swCount) :
			isolateAssert = Not( And ( Not(self.F(sw,pc1) == sw), self.F(sw,pc1) == self.F(sw,pc2)))
			self.z3Solver.add(isolateAssert)		

	def addBoundConstraints(self, xRange, pcRange) :
		self.z3Solver.add(self.pc < pcRange + 1)
		self.z3Solver.add(self.x < xRange + 1)




t = Topology()
c = ConstraintGenerator(t)
c.generateAssertions()