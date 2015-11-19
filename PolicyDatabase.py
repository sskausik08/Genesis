import networkx as nx
import metis

"""Policy Database is used to maintain the database of policies incorporated in the network. 
This will help in better bookmarking and aid in policy change synthesis."""
class PolicyDatabase(object) :
	def __init__(self) :
		self.pc = 0
		self.endpointTable = dict()
		self.waypointTable = dict()
		self.isolationTable = []
		self.mutlicastTable = dict()
		self.equalMulticastPolicy = dict()
		self.relClasses = []
		self.relClassGraphs = []
		self.relationalClassCreationFlag = False
		self.paths = dict()

	def addAllowPolicy(self, srcIP, srcSw, dstIP, dstSw, W=None) :
		""" srcSw = source IP next hop switch
			dstSw = Destination IP next hop switch
			W = List of Waypoints. """

		self.endpointTable[self.pc] = [srcIP, dstIP, srcSw, dstSw]
		if W == None : 
			self.waypointTable[self.pc] = []
		else :
			self.waypointTable[self.pc] = W

		self.relClasses.append([self.pc])
		self.pc += 1
		return self.pc - 1

	def getAllowPolicyCount(self) :
		return len(self.endpointTable)

	def getAllowPolicy(self, no) :
		""" Policy is of the form : [[srcIP, dstIP, srcSw, dstSw], Waypoints] """
		if no not in self.endpointTable : 
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

	def printPaths(self, topology) :
		for pc in range(self.getPacketClassRange()) :
			if not self.isMulticast(pc) :
				ep = self.endpointTable[pc]
				lpath = self.paths[pc]
				phypath = map(topology.getSwName, lpath)
				print "PC#" + str(pc) + ": Endpoint Information : " + str(ep) + " Path : " + str(phypath) 
			else :
				policy = self.mutlicastTable[pc]
				lpaths = self.paths[pc]
				phypaths = []
				for lpath in lpaths :
					phypaths.append(map(topology.getSwName, lpath))
				print "PC#" + str(pc) + ": Endpoint Information : " + str(policy) + " Path : " + str(phypaths)

	def addIsolationPolicy(self, ep1, ep2) :
		# Find the Packet Class numbers
		pc1 = -1
		pc2 = -1
		for i in self.endpointTable.keys() :
			ep = self.endpointTable[i]
			if ep[0] == ep1[0] and ep[1] == ep1[1] :
				pc1 = i
			if ep[0] == ep2[0] and ep[1] == ep2[1] :
				pc2 = i

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

		for relClass in self.relClasses : 
			self.createRelationalClassGraph(relClass)

		self.relationalClassCreationFlag = True
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
			if pc == pc2 or not self.isIsolated(pc,pc2) :
				continue

			path2 = self.getPath(pc2)

			for i in range(len(path1)) :
				try :
					# Find common switch.
					pos = path2.index(path1[i])

					# Check next hop is not equal.
					if i + 1 < len(path1) and pos + 1 < len(path2) :
						if path1[i+1] == path2[pos + 1] : 
							print "Packet Class #" + str(pc) + " violated isolation policy with Packet Class #" + str(pc2)
							print "DEBUG: PC#" + str(pc) + ":" + str(path1) + " PC#" + str(pc2) + ":" + str(path2) 
							return False
				except ValueError:
					continue

		return True

	def isMulticast(self, pc) :
		if pc in self.mutlicastTable :
			return True
		else :
			return False

	def isEqualMulticast(self, pc) :
		if pc in self.equalMulticastPolicy :
			return True
		else :
			return False

	def addEqualMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		self.mutlicastTable[self.pc] = [srcIP, srcSw, dstIPs, dstSws]
		self.equalMulticastPolicy[self.pc] = True 
		self.pc += 1
		return self.pc - 1

	def addMulticastPolicy(self, srcIP, srcSw, dstIPs, dstSws) :
		self.mutlicastTable[self.pc] = [srcIP, srcSw, dstIPs, dstSws]
		self.pc += 1
		return self.pc - 1

	def getMulticastPolicy(self, pc) :
		return self.mutlicastTable[pc]

	def getPacketClassRange(self) :
		return self.pc

	def getPacketClass(self, epIn) :
		""" Returns packet class for a pair of end-points"""

		i = 0
		for ep in self.endpointTable.values() :
			if ep[0] == epIn[0] and ep[1] == epIn[1] :
				return i
			i += 1

	def getSourceSwitch(self, pc) :
		if self.isMulticast(pc) :
			return self.mutlicastTable[pc][1]
		if pc not in self.endpointTable :
			raise LookupError(str(pc) + " is not a valid packet class flow number.")
		return self.endpointTable[pc][2]

	def createRelationalClassGraph(self, relClass) :
		""" Creation of a Graph of edges of each packet class in the relational Class to leverage policy interactions to 
		perform fuzzy synthesis"""

		G = nx.Graph()
		
		for pc in relClass :
			G.add_node(pc, switch=str(pc))

		for policy in self.isolationTable : 	
			if policy[0] in relClass : 
				G.add_edge(policy[0],policy[1])

		self.relClassGraphs.append(G)

		return G

	def getRelationalClassGraphs(self) :
		return self.relClassGraphs








