from z3 import *
from Topology import Topology

class ConstraintGenerator(object) :
	def __init__(self, topo) :
		self.topology = topo

		# Network Forwarding Function
		self.F = Function('F', IntSort(), IntSort(), IntSort())
		self.z3Solver = Solver()

	def generateAssertions(self) :	
		self.addReachabilityConstraints(1,2,1)
		self.addWaypointConstraints(1,2,1,[5])

		self.addReachabilityConstraints(1,2,2)

		self.addReachabilityConstraints(1,3,3)
		self.addWaypointConstraints(1,3,3,[5])

		self.addReachabilityConstraints(1,3,4)

		self.addReachabilityConstraints(1,3,5)

		self.addTrafficIsolationConstraints(4,5)
		self.addTrafficIsolationConstraints(3,5)
		self.addTrafficIsolationConstraints(4,3)
		
		print self.z3Solver.check()
		print self.z3Solver.model()

	# Returns F^n(x)
	def composeF(self, n, x, pc) :
		cf = x
		for i in range(n) :
			cf = self.F(cf,pc)
		return cf

	def addTopologyConstraints(self, pc) :
		swCount = self.topology.getSwitchCount()

		for sw in range(swCount) :
			neighbours = self.topology.getSwitchNeighbours(sw)

			# Add assertions to ensure f(sw,*) leads to a valid neighbour. 
			topoAssert = False

			for n in neighbours : 
				topoAssert = Or(topoAssert, self.F(sw,pc) == n)
			
			self.z3Solver.add(topoAssert)

	def addReachabilityConstraints(self, s, d, pc, isDest=True) :
		# Add topology constraint for this packet loss :
		self.addTopologyConstraints(pc)

		maxPathLen = self.topology.getMaxPathLength()
		reachAssert = False

		for i in range(1,maxPathLen + 1) :
			reachAssert = Or(reachAssert, self.composeF(i,s,pc) == d)

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,pc) must be zero. 
		# When we perform the translation to rules, we can forward it to host accordingly.

		if isDest :
			destAssert = (self.F(d,pc) == 0)
			self.z3Solver.add(destAssert)
	

	def addWaypointConstraints(self, s, d, pc, W) :
		for w in W :
			self.addReachabilityConstraints(s, w, pc, False)

	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		# Isolation of traffic for packet classes pc1 and pc2. 
		swCount = self.topology.getSwitchCount()

		for sw in range(swCount) :
			isolateAssert = Not( And ( self.F(sw,pc1) > 0, self.F(sw,pc1) == self.F(sw,pc2)))

			self.z3Solver.add(isolateAssert)		




t = Topology()
c = ConstraintGenerator(t)
c.generateAssertions()