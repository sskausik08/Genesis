import networkx as nx
#import metis
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

		# Zeppelin Domain assignment support
		self.subnetPacketClasses = dict()
		self.bgpExtensions = []


	def addReachabilityPolicy(self, predicate, srcSw, dstSw, W=None, len=None) :
		""" srcSw = source IP next hop switch
			dstSw = Destination IP next hop switch
			W = List of list of Waypoints. """

		self.endpointTable[self.pc] = [predicate, None, srcSw, dstSw]
		if W == None : 
			self.waypointTable[self.pc] = []
		else :
			self.waypointTable[self.pc] = W

		if not len == None :
			self.pathLengthTable[self.pc] = len

		self.relClasses.append([self.pc])
		
		if type(predicate) == int : 
			if predicate in self.subnetPacketClasses :
				self.subnetPacketClasses[predicate].append(self.pc)
			else : 
				self.subnetPacketClasses[predicate] = [self.pc]

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

	def getPredicate(self, no) : 
		if no not in self.endpointTable : 
			return None
		else :
			return self.endpointTable[no][0]

	def hasWaypoints(self, pc):
		""" Returns true or false if pc has waypoints """
		if pc not in self.endpointTable : 
			return False
		elif self.waypointTable[pc] == [] :
			return False
		else : 
			return True

	def getWaypoints(self, pc) :
		if self.hasWaypoints(pc) : 
			return self.waypointTable[pc]
		else : 
			return []

	def addPath(self, pc, path) :
		self.paths[pc] = path
		if len(path) > 0 :
			self.enforcementStatusTable[pc] = True # Policy #pc has been enforced. 

	def getPath(self, pc) :
		return self.paths[pc]

	def getPaths(self) :
		return self.paths

	def printPaths(self, topology) :
		output = open("genesis-paths.txt", 'w')
		for pc in range(self.getPacketClassRange()) :
			if pc in self.paths : 
				if not self.isMulticast(pc) :
					ep = self.endpointTable[pc]
					lpath = self.paths[pc]
					phypath = map(topology.getSwName, lpath)
					output.write("PC#" + str(pc) + ": Endpoint Information : " + ep[0].getStr() + " Path : " + str(phypath) + "\n")
				else :
					policy = self.mutlicastTable[pc]
					lpaths = self.paths[pc]
					phypaths = []
					for lpath in lpaths :
						phypaths.append(map(topology.getSwName, lpath))
					output.write("PC#" + str(pc) + ": Endpoint Information : " + str(policy) + " Path : " + str(phypaths) + "\n")

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
		
		waypoints = self.waypointTable[pc]
		if len(waypoints) == 0:
			return True

		prevWayptPos = -100
		for wset in waypoints : 
			# ordered sets 
			waypointFlag = True
			wayptPos = -1
			for w in wset :  
				foundFlag = False
				i = 0
				for sw in path : 
					if sw == w :
						foundFlag = True
						if i < prevWayptPos :
							# Not ordered correctly 
							return False
						if i > wayptPos : 
							wayptPos = i
						break
					i += 1
				waypointFlag = waypointFlag and foundFlag

			if not waypointFlag :
				return False

			prevWayptPos = wayptPos
		
		return True

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
		self.fwdRulesFile = open("genesis-forwarding-rules.txt", 'w')
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

	def getDestinationSubnet(self, pc) :
		""" Return the destination subnet label (predicate) for pc """
		return self.endpointTable[pc][0]

	def getDestinationSubnets(self) :
		""" Zeppelin Function: return destination subnet labels """
		dstSubnets = []
		for policy in self.endpointTable.values() : 
			if policy[0] not in dstSubnets : 
				dstSubnets.append(policy[0])

		return dstSubnets 

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

	def getDestinationSubnetPacketClasses(self, subnet) :
		if subnet not in self.subnetPacketClasses : 
			return []
		else :
			return self.subnetPacketClasses[subnet]

	def addBGPExtensions(self, bgpExtensions) :
		self.bgpExtensions = copy.deepcopy(bgpExtensions)

	def validateControlPlane(self, topology, staticRoutes, backups=[]) :
		violationCount = 0
		for pc in range(self.getPacketClassRange()) :
			src = self.getSourceSwitch(pc)
			dstSw = self.getDestinationSwitch(pc)
			dst = self.getDestinationSubnet(pc)
			dag = self.dags[dst]
			gpath = []
			nextsw = src
			while nextsw != dstSw : 
				path = topology.getShortestPath(nextsw, dstSw)
				if path[1] != dag[nextsw] and [nextsw, dag[nextsw]] not in staticRoutes[dst] : 
					violationCount += 1 
					print "Packet class violated by ZCP", pc 
					print path
					print dag
					print staticRoutes[dst]
					break
				nextsw = dag[nextsw]

			for tup in self.bgpExtensions : 
				if tup[3] != dst : continue
				if tup[1] != dstSw : continue
				nextsw = src
				while nextsw != dstSw : 
					zpath = topology.getShortestPath(nextsw, dstSw)
					zpath2 = topology.getShortestPath(nextsw, tup[2])
					if topology.getPathDistance(zpath) >= topology.getPathDistance(zpath2) and [nextsw, dag[nextsw]] not in staticRoutes[dst] : 
						violationCount += 1 
						print "BGP gateway violation by ZCP", pc 
						break
				nextsw = dag[nextsw]

		# Validate backup paths
		for dst in backups : 
			backupPaths = backups[dst]
			dag = self.dags[dst]
			for backupPath in backupPaths : 
				path = topology.getShortestPathStaticRoutes(backupPath[0], backupPath[len(backupPath) - 1], staticRoutes[dst], [])
				for i in range(len(path) - 1) : 
					nextPath = topology.getShortestPath(backupPath[0], backupPath[len(backupPath) - 1], [[path[i], path[i+1]]])
					if nextPath[1] != backupPath[1] : 
						print "Backup path violated" 
						print dag, backupPath, nextPath, staticRoutes[dst]
						violationCount += 1
						break

		if violationCount > 0 :
			print "Error: incorrect OSPF configuration"
			print "Number of Violations is", violationCount

	def validateControlPlaneResilience(self, topology, staticRoutes): 
		for pc in range(self.getPacketClassRange()) :
			dst = self.getDestinationSubnet(pc)
			path = self.paths[pc]
			srcSw = path[0]
			dstSw = path[len(path) - 1]

			routingLoopAbsence = True
			for index in range(len(path) - 1) :
				paths = topology.getAllShortestPathsStaticRoutes(srcSw, dstSw, staticRoutes[dst], [[path[index], path[index+1]]])
				rla = True
				if len(paths) == 0 : 
					print "Routing loop", dst, path, path[index], path[index+1], staticRoutes[dst]
					topology.getShortestPathStaticRoutes(srcSw, dstSw, staticRoutes[dst], [[path[index], path[index+1]]])
					rla = False
				routingLoopAbsence = routingLoopAbsence & rla

			if not routingLoopAbsence : 
				print "Violation, routing loop found" 

	def validateControlPlaneWaypointCompliance(self, topology, staticRoutes, waypoints, waypointPaths): 
		print staticRoutes
		# Waypoint Compliance
		for pc in range(self.getPacketClassRange()) :
			dst = self.getDestinationSubnet(pc)
			path = self.paths[pc]
			srcSw = path[0]
			dstSw = path[len(path) - 1]
			zpaths = topology.getAllShortestPathsStaticRoutes(srcSw, dstSw, staticRoutes[dst]) # Actual Path
			traverseWaypoint = True
			if dst not in waypoints : traverseWaypoint = True
			else :
				if len(zpaths) == 0 : 
					print "No path" 
					traverseWaypoint = False
				
				for zpath in zpaths : 
					pathWaypointTraverse = False
					for w in waypoints[dst] : 
						if w in zpath : 
							pathWaypointTraverse = True
					traverseWaypoint = traverseWaypoint & pathWaypointTraverse

			if not traverseWaypoint : 
				print "Packet Class", pc ,"did not traverse waypoint"
				print zpaths,  waypoints[dst]

		for pc in range(self.getPacketClassRange()) :
			dst = self.getDestinationSubnet(pc)
			path = self.paths[pc]
			srcSw = path[0]
			dstSw = path[len(path) - 1]
			path = topology.getShortestPathStaticRoutes(srcSw, dstSw, staticRoutes[dst]) #  one of the paths
			if [path[0], path[1]] in staticRoutes[dst] : 
				print "Source Static route.", pc
				continue

			wpathCount = 0
			for wpath in waypointPaths[dst] : 
				if wpath[0] == path[0] and wpath[len(wpath) - 1] == path[len(path) - 1] : 
					wpathCount += 1
			if wpathCount < 2 : 
				print "Single waypoint path", pc
				continue

			traverseWaypointResilience = True
			for index in range(len(path) - 1) :
				sharedLink = False
				for wpath in waypointPaths[dst] : 
					if wpath != path and wpath[0] == path[0] and path[index] in wpath and path[index+1] in wpath : 
						# Common link. Failure will disable both paths. Dont check this link failure
						sharedLink = True

				if sharedLink : continue 

				zpaths = topology.getAllShortestPathsStaticRoutes(srcSw, dstSw, staticRoutes[dst], [[path[index], path[index+1]]])
			
				traverseWaypoint = True
				if dst not in waypoints : traverseWaypoint = True
				else :
					if len(zpaths) == 0 : 
						print "No path", topology.getShortestPathStaticRoutes(srcSw, dstSw, staticRoutes[dst], [[path[index], path[index+1]]])
						traverseWaypoint = False
					
					for zpath in zpaths : 
						pathWaypointTraverse = False
						for w in waypoints[dst] : 
							if w in zpath : 
								pathWaypointTraverse = True
						traverseWaypoint = traverseWaypoint & pathWaypointTraverse

				if not traverseWaypoint : 
					print path, waypoints[dst]
					print path[index], path[index+1], zpaths 
					for zpath in zpaths : 
						print "AD", zpath, topology.getPathDistance(zpath), 
				traverseWaypointResilience = traverseWaypointResilience & traverseWaypoint

			if not traverseWaypointResilience : 
				print dst, 
				for wpath in waypointPaths[dst] : 
					print wpath, topology.getPathDistance(path)
				print "Violation, did not traverse waypoints under failures", pc

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



