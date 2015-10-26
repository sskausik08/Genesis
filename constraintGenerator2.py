from z3 import *
from Topology import Topology
import time
import random

class ConstraintGenerator2(object) :
	def __init__(self, topo) :
		self.topology = topo

		# Network Forwarding Function
		self.F = Function('F', IntSort(), IntSort(), IntSort(), IntSort(), BoolSort())
		# Transitioning from F to F1 to see any changes. 
		self.F1 = Function('F1', IntSort(), IntSort(), IntSort(), BoolSort())
		self.R = Function('R', IntSort(), IntSort(), IntSort(), BoolSort())
		self.x = Int('x')  # Generic variable for nodes.
		self.pc = Int('pc') # Generic variable for packet classes
		self.z3Solver = Solver()
		self.fwdmodel = None 

	def generateAssertions(self) :	

		start_t = time.time()
		print "Adding Constraints at " + str(start_t)

		# Add Bound Constraints on x and pc.
		self.addBoundConstraints(self.topology.getSwitchCount() - 1, 5)
		self.addTopologyConstraints()
		

		self.addFinalReachabilityConstraints(1,3,1,self.topology.getMaxPathLength())
		self.addWaypointConstraints(1,3,1,[4,5])

		#self.addNeighbourConstraints()
		# for i in range(1, self.topology.getMaxPathLength() + 1) :
		# 	self.z3Solver.push()
		# 	self.addFinalReachabilityConstraints(1,3,1,i)
		# 	self.addWaypointConstraints(1,3,1,[4,5])
		# 	sat = self.z3Solver.check()
		# 	if sat == z3.sat : 
		# 		print "Sat " + str(i)
		# 		break
		# 	else :
		# 		print "unsat " + str(i)
		# 		self.z3Solver.pop()

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


		self.addReachabilityConstraints(1,3,3,self.topology.getMaxPathLength())
		# self.addReachabilityConstraints(1,3,4,self.topology.getMaxPathLength())

		# self.addReachabilityConstraints(1,3,5,self.topology.getMaxPathLength())
		

		self.addTrafficIsolationConstraints(1,3)
		# self.addTrafficIsolationConstraints(3,5)
		# # self.addTrafficIsolationConstraints(4,3)

		# sat = self.z3Solver.check()
		
	
		# for i in range(1,50):
		# 	if i % 2 == 0 :
		# 		s = 1
		# 	else :
		# 		s = 2

		# 	d = random.randint(8,10)
		# 	self.addFinalReachabilityConstraints(s,d,i,self.topology.getMaxPathLength())
		# 	self.addWaypointConstraints(s,d,i, [random.randint(3,5), random.randint(6,7)])

		# 	if(i > 2) :
		# 		self.addTrafficIsolationConstraints(i, i - 1)


		self.z3Solver.check()
		self.fwdmodel = self.z3Solver.model()
		print self.fwdmodel
		
		# print self.fwdmodel.evaluate(self.F(1,2,1,1))
		# print self.fwdmodel.evaluate(self.F(2,1,1,1))

		end_t = time.time()
		print "Time taken to solve the constraints is" + str(end_t - start_t)
		#print self.getPath(1,1)

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
				neighbourAssert = self.R(sw,n,self.pc) == True
				unreachedAssert = And(unreachedAssert, self.R(sw,n,self.pc) == False)
				for n1 in neighbours :
					if n == n1 : 
						continue
					else :
						neighbourAssert = And(neighbourAssert, self.R(sw,n1,self.pc) == False)
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
					self.z3Solver.add(ForAll(self.pc, self.R(sw,s,self.pc) == False))

	# def addNeighbourConstraints(self) :
	# 	swCount = self.topology.getSwitchCount()
	# 	for sw in range(0,swCount) :
	# 		neighbours = self.topology.getSwitchNeighbours(sw)

	# 		for i in range(swCount+1) : 
	# 			if i in neighbours : 
	# 				self.z3Solver.add(self.N(sw,i) == True)
	# 			else :
	# 				self.z3Solver.add(self.N(sw,i) == False)

	def addFinalReachabilityConstraints(self, s, d, pc, pathlen, isDest=True) :

		# Add topology constraint for this packet class :
		#self.addTopologyConstraints(pc)
		reachAssert = self.F1(d,pc,pathlen) == True

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(d)

		if isDest : 
			destAssert = True
			for n in neighbours :
				destAssert = And(destAssert, self.R(d,n,pc) == False)

			self.z3Solver.add(destAssert)

		# Add Path Constraints
		self.addPathConstraints(s,d,pc)

	def addReachabilityConstraints(self, s, d, pc, isDest=True) :

		# Add topology constraint for this packet class :
		#self.addTopologyConstraints(pc)
		maxPathLen = self.topology.getMaxPathLength()
		reachAssert = self.F1(d,pc,maxPathLen) == True

		self.z3Solver.add(reachAssert)

		# If Destination, then forwarding has to stop here. So, F(d,neighbour(d),pc,1) == False 
		# When we perform the translation to rules, we can forward it to host accordingly.
		
		neighbours = self.topology.getSwitchNeighbours(d)

		if isDest : 
			destAssert = True
			for n in neighbours :
				destAssert = And(destAssert, self.R(d,n,pc) == False)

			self.z3Solver.add(destAssert)

		# Add Path Constraints
		self.addPathConstraints(s,d,pc)

	def addWaypointConstraints(self, s, d, pc, W) :
		for w in W :
			self.addReachabilityConstraints(s, w, pc, False)

	def addPathConstraints(self,s,d,pc) :
		l = Int('l')
		self.z3Solver.add(l > 0)
		self.z3Solver.add(l < self.topology.getMaxPathLength() + 1)
		# s1 = Int('s1')
		# d1 = Int('d1')
		# reachedAssert = ForAll(self.pc, ForAll(s1, ForAll(d1, ForAll(l, (Implies (self.F(s1,d1,self.pc,l-1), self.F(s1,d1,self.pc,l)))))))
		# w = Int('w')
		# nextHopAssert = Implies(And(self.F(s1,w,self.pc,l),self.F(w,d1,self.pc,1)),self.F(s1,d1,self.pc,l+1))
		# nextHopAssert = And(nextHopAssert, Implies(self.F(s,d,self.pc,l+1),And(self.F(s,w,self.pc,l),self.F(w,d,self.pc,1))))
		# pathAssert = ForAll(self.pc, ForAll(s1, ForAll(d1, ForAll(w, ForAll(l, And(nextHopAssert, self.N(w,d1)))))))

		#self.z3Solver.add(reachedAssert)
		# self.z3Solver.add(pathAssert)

		neighbours = self.topology.getSwitchNeighbours(s)

		# Add assertions to ensure f(s,*) leads to a valid neighbour. 
		neighbourAssert = False
		f1Assert = True
		negf1Assert = True
		for n in neighbours :
			neighbourAssert = Or(neighbourAssert, self.R(s,n,pc) == True)
			f1Assert = And(f1Assert, Implies(self.R(s,n,pc) == True, self.F1(n,pc,1) == True))
			negf1Assert = And(negf1Assert, Implies(self.R(s,n,pc) == False, self.F1(n,pc,1) == False))

		self.z3Solver.add(neighbourAssert)
		self.z3Solver.add(f1Assert)
		self.z3Solver.add(negf1Assert)

		
		swCount = self.topology.getSwitchCount()
		maxPathLen = self.topology.getMaxPathLength()


		for i in range(1,swCount+1) :
			if i == s : 
				for pathlen in range(2,maxPathLen+1) :	
					reachedAssert = (Implies (self.F1(i,pc,pathlen-1), self.F1(i,pc,pathlen)))
					self.z3Solver.add(reachedAssert)
				continue
			self.z3Solver.add(self.F1(s,pc,0) == True)

			for pathlen in range(2,maxPathLen+1) :	
				reachedAssert = (Implies (self.F1(i,pc,pathlen-1), self.F1(i,pc,pathlen)))
				self.z3Solver.add(reachedAssert)

			ineighbours = self.topology.getSwitchNeighbours(i) 

			neighbourAssert = False

			for isw in ineighbours : 
				for pathlen in range(1,maxPathLen) :
					nextHopAssert = Implies(And(self.F1(i,pc,pathlen) == True,self.R(i,isw,pc) == True),self.F1(isw,pc,pathlen+1) == True)
					self.z3Solver.add(nextHopAssert)

				unreachedAssert = Implies(self.F1(i,pc,maxPathLen) == False, self.R(i,isw,pc) == False)
				self.z3Solver.add(unreachedAssert)	

			
			# Paths of length 2.
			path2Assert = True
			for pathlen in range(2,maxPathLen+1) :
				beforeHopAssert = False
				for isw in ineighbours : 
					beforeHopAssert = Or(beforeHopAssert, And(self.R(isw, i, pc) == True, self.F1(isw, pc, pathlen - 1) == True))
				
				path2Assert = And(path2Assert, Implies(self.F1(i,pc,pathlen), beforeHopAssert))

			path1Assert = Implies(self.F1(i,pc,1),self.R(s,i,pc)) 
			self.z3Solver.add(path1Assert)
			#self.z3Solver.add(Or(path1Assert, path2Assert))
			self.z3Solver.add(path2Assert)
			# Path len > 1 always.
			self.z3Solver.add(self.F1(i,pc,0) == False)



	def addTrafficIsolationConstraints(self, pc1, pc2) : 
		# Isolation of traffic for packet classes pc1 and pc2. 
		swCount = self.topology.getSwitchCount()

		for sw in range(1, swCount + 1) :
			for n in self.topology.getSwitchNeighbours(sw) :
				isolateAssert = Not( And (self.R(sw,n,pc1) == True, self.R(sw,n,pc2) == True))
				self.z3Solver.add(isolateAssert)		

	def addBoundConstraints(self, xRange, pcRange) :
		self.z3Solver.add(self.pc < pcRange + 1)
		self.z3Solver.add(self.x < xRange + 1)

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
		




t = Topology()
c = ConstraintGenerator2(t)
c.generateAssertions()
