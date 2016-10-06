import networkx as nx
import metis
import copy

"""Policy Database is used to maintain the database of policies incorporated in the network. 
This will help in better bookmarking and aid in policy change synthesis."""
class PolicyDatabase(object) :
	def __init__(self) :
		self.pc = 0
		self.endpointTable = dict()
		self.waypointTable = dict()
		self.pathLengthTable = dict()
		self.enforcementStatusTable = dict()
		self.isolationTable = []
		self.isolationMap = dict()
		self.mutlicastTable = dict()
		self.equalMulticastPolicy = dict()
		self.relClasses = []
		self.relClassGraphs = []
		self.relationalClassCreationFlag = False
		self.paths = dict()
		self.switchTableConstraints = []
		self.linkCapacityConstraints = []
		self.minimizeAverageUtilizationTEFlag = False
		self.minimizeMaxUtilizationTEFlag = False
		
		# Support for topology 
		self.sliceEndpointTable = dict()
		self.sliceWaypointTable = dict()
		self.originalPacketClasses = dict()


		# Support for storing DAGs for control plane generation
		self.dags = dict()


	def addReachabilityPolicy(self, predicate, srcSw, dstSw, W=None, len=None) :
		""" srcSw = source IP next hop switch
			dstSw = Destination IP next hop switch
			W = List of Waypoints. """

		self.endpointTable[self.pc] = [predicate, None, srcSw, dstSw]
		if W == None : 
			self.waypointTable[self.pc] = []
		else :
			self.waypointTable[self.pc] = W

		if not len == None :
			self.pathLengthTable[self.pc] = len

		self.relClasses.append([self.pc])
		self.pc += 1
		return self.pc - 1

	def getReachabilityPolicyCount(self) :
		return len(self.endpointTable)

	def getReachabilityPolicy(self, no) :
		""" Policy is of the form : [[predicate, None, srcSw, dstSw], Waypoints, length] """
		if no not in self.endpointTable : 
			return None
		policy = [self.endpointTable[no]]
		if self.waypointTable[no] == [] :
			policy.append([])
		else :
			policy.append(self.waypointTable[no])
		if no in self.pathLengthTable :
			policy.append(self.pathLengthTable[no])
		else :
			policy.append(0)
		return policy

	def hasWaypoints(self, pc):
		""" Returns true or false if pc has waypoints """
		if pc not in self.endpointTable : 
			return False
		elif self.waypointTable[pc] == [] :
			return False
		else : 
			return True

	def addPath(self, pc, path) :
		self.paths[pc] = path
		if len(path) > 0 :
			self.enforcementStatusTable[pc] = True # Policy #pc has been enforced. 

	def getPath(self, pc) :
		return self.paths[pc]

	def printPaths(self, topology) :
		for pc in range(self.getPacketClassRange()) :
			if pc in self.paths : 
				if not self.isMulticast(pc) :
					ep = self.endpointTable[pc]
					lpath = self.paths[pc]
					phypath = map(topology.getSwName, lpath)
					print "PC#" + str(pc) + ": Endpoint Information : " + ep[0].getStr() + " Path : " + str(phypath) 
				else :
					policy = self.mutlicastTable[pc]
					lpaths = self.paths[pc]
					phypaths = []
					for lpath in lpaths :
						phypaths.append(map(topology.getSwName, lpath))
					print "PC#" + str(pc) + ": Endpoint Information : " + str(policy) + " Path : " + str(phypaths)

	def addIsolationPolicy(self, pc1, pc2) :
		if pc1 > pc2 : 
			pc1, pc2 = pc2, pc1 

		if pc1 in self.isolationMap : 
			if pc2 in self.isolationMap[pc1] :
				# Isolation Policy already added.
				return 

		self.isolationTable.append([pc1,pc2])
		if pc1 in self.isolationMap : 
			self.isolationMap[pc1].append(pc2)
		else :
			self.isolationMap[pc1] = [pc2]

		if pc2 in self.isolationMap : 
			self.isolationMap[pc2].append(pc1)
		else :
			self.isolationMap[pc2] = [pc1]

	def getIsolationPolicy(self, no) :
		if no > len(self.isolationTable) - 1 : 
			return None
		else :
			return self.isolationTable[no]

	def isIsolated(self, pc1, pc2) :
		if pc1 in self.isolationMap:
			if pc2 in self.isolationMap[pc1] :
				return True
		return False

	def getIsolationPolicyCount(self) :
		return len(self.isolationTable)

	def getIsolatedPolicies(self, pc) :
		""" returns all packet classes isolated to pc"""
		if pc in self.isolationMap : 
			return self.isolationMap[pc]
		else :
			return []

	def createRelationalClasses(self) :
		""" Create Relational classes of packet classes. A relational class is a maximal set of
		packet classes which need to be synthesised together because of inter-class policies like
		isolation """

		# If link capacity policies exist, or global traffic engineering constraints, No relational classes!
		if len(self.getLinkCapacityConstraints()) > 0 or len(self.getSwitchTableConstraints()) > 0 or self.trafficEngineeringEnabled() : 
			self.relationalClassCreationFlag = True
			self.relClasses = []
			self.relClasses.append(range(self.getPacketClassRange()))	
		else : 
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


		# Clear graphs as we re-create them. 
		self.relClassGraphs = []

		for relClass in self.relClasses :
			self.createRelationalClassGraph(relClass)

		self.relationalClassCreationFlag = True
		return self.relClasses

	def getRelationalClass(self, pc) :
		""" Returns the relational class containing pc"""

		for relClass in self.relClasses :
			if pc in relClass :
				return relClass

	def getRelationalClasses(self) :
		return self.relClasses

	def getUnenforcedRelationalClasses(self):
		unenforcedRCs = []
		for relClass in self.relClasses :
			for pc in relClass :
				if not pc in self.enforcementStatusTable:
					unenforcedRCs.append(relClass)
					break
		return unenforcedRCs

	def getUnenforcedRelationalClassGraphs(self):
		unenforcedRCs = []
		for relClass in self.relClasses :
			for pc in relClass :
				if not pc in self.enforcementStatusTable:
					unenforcedRCs.append(relClass)
					break
		return unenforcedRCs

	def isEnforced(self, pc):
		return pc in self.enforcementStatusTable 

	def validatePolicies(self, topology) :
		for pc in range(self.getPacketClassRange()) :
			if pc in self.paths : 
				validFlag = topology.validatePath(self.getPath(pc)) and self.validateReachabilityPolicy(pc) and self.validateIsolationPolicy(pc)
				if not validFlag : 
					print "Policy " + str(pc) + " not enforced correctly."
					print "Topology Validation", topology.validatePath(self.getPath(pc))
					print "Reachability Validation", self.validateReachabilityPolicy(pc)
					print "Isolation Validation", self.validateIsolationPolicy(pc)
					return False
			else : 
				print "Policy " + str(pc) + " not enforced."
				return False

		return self.validateCapacityPolicy()

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

	def validateReachabilityPolicy(self, pc) :
		path = self.getPath(pc)
		policy = self.endpointTable[pc]
		if not path[0] == policy[2] :
			return False
		if not path[len(path) - 1] == policy[3]:
			return False
		return True
		# waypoints = self.waypointTable[pc]
		# if len(waypoints) == 0:
		# 	return True

		# waypointFlag = True
		# for w in waypoints : 
		# 	foundFlag = False
		# 	for sw in path : 
		# 		if sw == w :
		# 			foundFlag = True
		# 			break
		# 	waypointFlag = waypointFlag and foundFlag
		# return waypointFlag 

	def validateCapacityPolicy(self):
		for policy in self.linkCapacityConstraints : 
			capacity = policy[2]
			sw1 = policy[0]
			sw2 = policy[1]
			for pc in self.paths : 
				path = self.paths[pc]
				try :
					pos = path.index(sw1)
					if pos + 1 < len(path) and path[pos + 1] == sw2 : 
						# Link used. 
						capacity -= 1
				except ValueError :
					continue

			if capacity < 0 : 
				return False
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
		if pc in self.endpointTable :
			return self.endpointTable[pc][2]
		elif pc in self.sliceEndpointTable:
			return self.sliceEndpointTable[pc][2]
		else :
			raise LookupError(str(pc) + " is not a valid packet class flow number.")


	def getDestinationSwitch(self, pc):
		if self.isMulticast(pc) :
			return self.mutlicastTable[pc][3]
		if pc in self.endpointTable :
			return self.endpointTable[pc][3]
		elif pc in self.sliceEndpointTable:
			return self.sliceEndpointTable[pc][3]
		else : 
			raise LookupError(str(pc) + " is not a valid packet class flow number.")
		

	def createRelationalClassGraph(self, relClass) :
		""" Creation of a Graph of edges of each packet class in the relational Class to leverage policy interactions to 
		perform DC synthesis"""

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

	def getRelationalClassGraphDegree(self, pc) :
		count = 0
		for policy in self.isolationTable :
			if (policy[0] == pc) or (policy[1] == pc) : 
				count += 1
		return count

	def addSwitchTableConstraint(self, sw, size) :
		self.switchTableConstraints.append([sw, size])

	def getSwitchTableConstraints(self):
		return self.switchTableConstraints

	def addLinkCapacityConstraint(self, sw1, sw2, capacity) :
		self.linkCapacityConstraints.append([sw1, sw2, capacity])

	def getLinkCapacityConstraints(self) :
		return self.linkCapacityConstraints

	def addSliceReachabilityPolicy(self, originalpc, srcSw, dstSw, W=None):
		""" Adds a temporary reach Policy. """
		print "Adding", srcSw, dstSw
		self.originalPacketClasses[self.pc] = originalpc
		self.sliceEndpointTable[self.pc] = [None, None, srcSw, dstSw]
		if not W == None :  
			print "Slice waypoints added", W
			self.sliceWaypointTable[self.pc] = W
		self.pc += 1
		return self.pc - 1		

	def getSliceReachabilityPolicy(self, pc) :
		""" Returns a slice reach Policy """
		if pc in self.endpointTable : 
			return self.getReachabilityPolicy(pc)

		if pc in self.sliceWaypointTable : 
			return [self.sliceEndpointTable[pc],  self.sliceWaypointTable[pc]]
		else :
			return [self.sliceEndpointTable[pc], []]

	def getOriginalPacketClass(self, pc) :
		if pc in self.endpointTable : 
			return pc
		else : 
			return self.originalPacketClasses[pc]

	def clearSliceReachabilityPolicies(self) :
		""" Clear slice Reachability Policies """
		# Find least pc.
		minpc = 100000000
		for pc in self.sliceEndpointTable  :
			if pc < minpc : 
				minpc = pc
		# Restore self.pc to minpc
		self.pc = minpc

		# Clear tables. 
		self.sliceEndpointTable = dict()
		self.sliceWaypointTable = dict()
		self.originalPacketClasses = dict()

	def writeForwardingRulesToFile(self, topology) :
		self.fwdRulesFile = open(".genesis-forwarding-rules", 'w')
		for pc in self.endpointTable.keys() :
			policy = self.endpointTable[pc]
			predicate = policy[0]
			if pc in self.paths : 
				path = self.getPath(pc)
			else : 
				continue
			i = 0
			while i < len(path) - 1 :
				self.fwdRulesFile.write(predicate.getStr() + " : " + topology.getSwName(path[i]) + " > " + topology.getSwName(path[i + 1]) + "\n")
				i += 1

	def getDestinations(self) : 
		dsts = []
		for policy in self.endpointTable.values() : 
			if policy[3] not in dsts : 
				dsts.append(policy[3])

		return dsts 
		
	def getDAGSources(self, dst, dStart) :
		# Return all sources which have dStart in the path
		srcs = []
		for pc in range(self.getPacketClassRange()) : 
			policy = self.endpointTable[pc]
			if policy[3] == dst : 
				path = self.getPath(pc) 
				if dStart in path : 
					srcs.append(path[0])
		
		return srcs
		
	def addDestinationDAG(self, dst, dag) : 
		self.dags[dst] = dag

	def getDestinationDAGs(self) : 
		return self.dags

	def validateControlPlane(self, topology, routefilters, t_res) :
		violationCount = 0
		for pc in range(self.getPacketClassRange()) :
			src = self.getSourceSwitch(pc)
			dst = self.getDestinationSwitch(pc)
			zpath = topology.getShortestPath(src, dst, routefilters[dst])
			dag = self.dags[dst]
			gpath = []
			nextsw = src
			while nextsw <> None : 
				gpath.append(nextsw)
				nextsw = dag[nextsw] 

			if zpath <> gpath : 
				if topology.getPathDistance(gpath) == topology.getPathDistance(zpath) :
					print "Path is not uniquely shortest for PC", pc
					violationCount += 1
				else :
					print "G", gpath, "Z", zpath, "shortest path is", topology.getShortestPath(src,dst)
					print "Not Shortest Path in control plane for class", pc
					print "Genesis path distance:", topology.getPathDistance(gpath), " Zeppelin: ", topology.getPathDistance(zpath)
					violationCount += 1
			if not topology.checkUniquenessShortestPath(zpath, routefilters[dst]) :
				print "Path is not uniquely shortest for PC", pc
				print zpath, 
				violationCount += 1
			if t_res > 0 :
				if not topology.checkResilience(src, dst, t_res, copy.deepcopy(routefilters[dst])) : 
					print "Not resilient", pc, self.getSourceSwitch(pc)
					violationCount += 1
		print "Number of Violations is", violationCount

	# def removeRedundantFilters(self, topology, routefilters) : 


	def addTrafficEngineeringObjective(self, minavg=False, minmax=False) :
		""" Add a traffic engineering objective """
		if minavg : 
			self.minimizeAverageUtilizationTEFlag = True
		elif minmax : 
			self.minimizeMaxUtilizationTEFlag = True

	def trafficEngineeringEnabled(self) : 
		return self.minimizeAverageUtilizationTEFlag or self.minimizeMaxUtilizationTEFlag
	
	def minimizeAverageUtilizationTE(self) :
		return self.minimizeAverageUtilizationTEFlag

	def minimizeMaxUtilizationTE(self) :
		return self.minimizeMaxUtilizationTEFlag



