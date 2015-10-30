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

		# Policy Database. 
		self.pdb = PolicyDatabase()
		
		start_t = time.time()
		print "Adding Constraints at " + str(start_t)

		# Add Packet Class Agnostic Constraints 
		self.addTopologyConstraints()

		
		
	
		# for i in range(3, self.topology.getMaxPathLength() + 1) :
		# 	self.z3Solver.push()
		# 	self.addReachabilityConstraints("1.2", 1, "1.3", 2, [5])
		# 	#self.addWaypointConstraints(1,3,1,[4,5])
		# 	sat = self.z3Solver.check()
		# 	if sat == z3.sat : 
		# 		print "Sat " + str(i)
		# 		break
		# 	else :
		# 		print "unsat " + str(i)
		# 		self.z3Solver.pop()

		# for i in range(1, self.topology.getMaxPathLength() + 1) :
		# 	self.z3Solver.push()
		# 	self.addReachabilityConstraints(1,2,2,i)
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
		# 	self.addReachabilityConstraints(s,d,i,self.topology.getMaxPathLength())
		# 	self.addWaypointConstraints(s,d,i, [random.randint(3,5), random.randint(6,7)])

		# 	if(i > 2) :
		# 		self.addTrafficIsolationConstraints(i, i - 1)

		# Generate the assertions.
		self.addPolicies()
		self.enforcePolicies()

		
		#print self.fwdmodel

		end_t = time.time()
		print self.pdb.getPath(1)
		print self.pdb.validateIsolationPolicy(1)
		print "Time taken to solve the constraints is" + str(end_t - start_t)
	
	def addPolicies(self) :
		self.addReachabilityPolicy("1.2", 1, "1.3", 2, [4,6])
		self.addReachabilityPolicy("1.3", 1, "1.4", 2)
		self.addReachabilityPolicy("1.4", 1, "1.4", 2)
		self.addTrafficIsolationPolicy(["1.2", "1.3"] , ["1.3", "1.4"])
		self.addTrafficIsolationPolicy(["1.4", "1.4"] , ["1.3", "1.4"])

		self.addReachabilityPolicy("2.4", 1, "2.4", 2)
		self.addReachabilityPolicy("2.5", 1, "2.5", 2)
		self.addReachabilityPolicy("2.6", 1, "2.6", 2)
		self.addTrafficIsolationPolicy(["2.4", "2.4"] , ["2.5", "2.5"])
		#self.addTrafficIsolationPolicy( ["1.4", "1.4"], ["2.5", "2.5"])

	def addReachabilityPolicy(self, srcIP, s, dstIP, d, W=None) :
		""" s = next hop switch of source host(s) 
			d = next hop switch of destination host(s)
			W = Waypoint Set (list of nodes) """

		# Add policy to PDB : 
		pc = self.pdb.addAllowPolicy(srcIP, s, dstIP, d, W)

	def addTrafficIsolationPolicy(self, ep1, ep2) : 
		# Isolation of traffic for packet classes (end-points) ep1 and ep2. 
		pc = self.pdb.addIsolationPolicy(ep1,ep2) # Returns [pc1,pc2]

	def enforcePolicies(self) :
		""" Enforcement of Policies stored in the PDB. """
		# Create Relational Packet Classses.
		relClasses = self.pdb.createRelationalClasses()

		for relClass in relClasses :
			# Independent Synthesis of relClass.
			self.z3Solver.push()
			for pc in relClass : 
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

	def addReachabilityConstraints(self, srcIP, srcSw, dstIP, dstSw, pc, W=None, pathlen=0) :
		if pathlen == 0 :
			# Default argument. Set to max.
			pathlen = self.topology.getMaxPathLength()

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




"""Policy Database is used to maintain the database of policies incorporated in the network. 
This will help in better bookmarking and aid in policy change synthesis."""
class PolicyDatabase(object) :
	def __init__(self) :
		self.pc = 0
		self.endpointTable = []
		self.waypointTable = []
		self.isolationTable = []
		self.relClasses = []
		self.paths = dict()

	def addAllowPolicy(self, srcIP, srcSw, dstIP, dstSw, W=None) :
		""" srcSw = source IP next hop switch
			dstSw = Destination IP next hop switch
			W = List of Waypoints. """

		self.endpointTable.append([srcIP, dstIP, srcSw, dstSw])
		if W == None : 
			self.waypointTable.append([])
		else :
			self.waypointTable.append(W)

		self.relClasses.append([self.pc])
		self.pc += 1
		return self.pc - 1

	def getAllowPolicyCount(self) :
		return len(self.endpointTable)

	def getAllowPolicy(self, no) :
		""" Policy is of the form : [[srcIP, dstIP, srcSw, dstSw], Waypoints] """
		if no > len(self.endpointTable) - 1 : 
			return None
		else :
			if self.waypointTable[no] == [] :
				return [self.endpointTable[no],None] 
			else :
				return [self.endpointTable[no], self.waypointTable[no]]

	def addPath(self, pc, path) :
		self.paths[pc] = path

	def getPath(self, pc) :
		return self.paths[pc]

	def addIsolationPolicy(self, ep1, ep2) :
		# Find the Packet Class numbers
		i = 0
		pc1 = -1
		pc2 = -1
		for ep in self.endpointTable :
			if ep[0] == ep1[0] and ep[1] == ep1[1] :
				pc1 = i 
			if ep[0] == ep2[0] and ep[1] == ep2[1] :
				pc2 = i
			i += 1	

		if pc1 == -1 :
			#Flows dont exist. 
			raise LookupError(srcIP1 + "->" + dstIP1 + " is not a valid packet class flow.")
		elif pc2 == -1 :
			raise LookupError(srcIP1 + "->" + dstIP2 + " is not a valid packet class flow.")
		else : 
			self.isolationTable.append([pc1,pc2])

		return [pc1,pc2]

	def getIsolationPolicy(self, no) :
		if no > len(self.isolationTable) - 1 : 
			return None
		else :
			return self.isolationTable[no]

	def isIsolated(self, pc1, pc2) :
		for policy in self.isolationTable :
			if (policy[0] == pc1 and policy[1] == pc2) or (policy[1] == pc1 and policy[0] == pc2) : 
				return True
		return False




	def getIsolationPolicyCount(self) :
		return len(self.isolationTable)

	def createRelationalClasses(self) :
		""" Create Relational classes of packet classes. A relational class is a maximal set of
		packet classes which need to be synthesised together because of inter-class policies like
		isolation """

		# For now, our inter-class policy is isolation.
		for pno in range(self.getIsolationPolicyCount()) :
			pc = self.getIsolationPolicy(pno)
			pc1 = pc[0]
			pc2 = pc[1]
			pc1rc = None
			pc2rc = None
			for relClass in self.relClasses :
				if pc1 in relClass : 
					pc1rc = relClass
				if pc2 in relClass :
					pc2rc = relClass

			# If pc1rc and pc2rc are same, dont do anything.
			if pc1rc == pc2rc and not pc1rc == None :
				continue # Both are in same relational class, dont do anything. 
			elif not pc1rc == None and pc2rc == None : 
				pc1rc.append(pc2)
			elif pc1rc == None and not pc2rc == None : 
				pc2rc.append(pc1)
			elif pc1rc == None and pc2rc == None :
				rc = [pc1,pc2]
				self.relClasses.append(rc)
			else :
				# Both are in different packet classes. Join them.
				pc1rc.extend(pc2rc)
				self.relClasses.remove(pc2rc)
			print self.relClasses

		return self.relClasses

	def getRelationalClass(self, pc) :
		""" Returns the relational class containing pc"""

		for relClass in self.relClasses :
			if pc in relClass :
				return relClass

	def validateIsolationPolicy(self, pc) :

		""" Validation of packet class flow pc w.r.t all its isolation policies"""
		path1 = self.getPath(pc)

		relClass = self.getRelationalClass(pc)

		for pc2 in relClass : 
			if pc == pc2 or self.isIsolated(pc,pc2) :
				continue

			path2 = self.getPath(pc2)

			for i in range(len(path1)) :
				try :
					# Find common switch.
					pos = path2.index(path1[i])

					# Check next hop is not equal.
					if i + 1 < len(path1) and pos + 1 < len(path2) :
						if path1[i+1] == path2[pos + 1] : 
							return False
				except ValueError:
					continue

		return True

	def getPacketClassRange(self) :
		return self.pc

	def getPacketClass(self, epIn) :
		""" Returns packet class for a pair of end-points"""

		i = 0
		for ep in self.endpointTable :
			if ep[0] == epIn[0] and ep[1] == epIn[1] :
				return i
			i += 1

	def getSourceSwitch(self, pc) :
		if pc > len(self.endpointTable) :
			raise LookupError(str(pc) + " is not a valid packet class flow number.")
		return self.endpointTable[pc][2]

t = Topology()
c = ConstraintGenerator2(t)