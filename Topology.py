class NetworkDatabase(object) :
	""" Database to store the switch mappings to integers """

	def __init__(self) :
		self.switchMap = ["dropSwitch"]
		self.swID = 1
		self.hostMap = dict()

	def insertSwitch(self, swName) :
		self.switchMap.append(swName)
		self.swID += 1
		return self.swID - 1

	def existsSwitch(self, swName) :
		for i in range(len(self.switchMap)) :
			if swName == self.switchMap[i] :
				return True
		return False

	def insertHost(self, hostName, swName) :
		sw = self.getSwID(swName)
		hostMap[hostName] = sw

	def getSwID(self, swName) :
		for i in range(len(self.switchMap)) :
			if swName == self.switchMap[i] :
				return i

		raise LookupError(str(swName) + " not in the network database")

	def getSwitchName(self, swID) :
		if swID > len(self.switchMap) - 1 :
			raise LookupError(str(swID) + " is not a valid switch ID")
		else :
			return self.switchMap[swID]

	def getSwitchCount(self) :
		return len(self.switchMap)

	def printSwitchMappings(self) :
		i = 0 
		for sw in self.switchMap : 
			print swName, ":", i
			i += 1

class Topology(object):
	"Class for a Topology"
	def __init__(self, name="topo-0"):
		self.name = name
		self.networkDatabase = NetworkDatabase()
		self.neighbours = dict()

	def getName(self) :
		return self.name

	def addSwitch(self, name, neighbours) :
		if not self.networkDatabase.existsSwitch(name):
			swID = self.networkDatabase.insertSwitch(name)
			self.neighbours[swID] = []
		else :
			swID = self.networkDatabase.getSwID(name)

		for n in neighbours :
			if not self.networkDatabase.existsSwitch(n) :
				nID = self.networkDatabase.insertSwitch(n)
				self.neighbours[nID] = []
			else :
				nID = self.networkDatabase.getSwID(n)

			if not nID in self.neighbours[swID] :
				self.neighbours[swID].append(nID)
			if not swID in self.neighbours[nID] :
				self.neighbours[nID].append(swID)

	def getSwID(self, swName) :
		return self.networkDatabase.getSwID(swName)

	def getSwName(self, swID) :
		return self.networkDatabase.getSwitchName(swID)

	def getMaxPathLength(self) :
		return 10
		
	def getSwitchCount(self) :
		return self.networkDatabase.getSwitchCount() - 1

	def getSwitchNeighbours(self, swID) :
		return self.neighbours[swID]

	def findTopologyBridges(self) :
		""" Uses Schmidt Chain Decomposition Algorithm to find the bridges in the topology """ 
		swCount = self.getSwitchCount()
		self.visited = dict() # Stores if swID has been visited
		self.dfSwList = [] # Stores the swIDs in order of DFS. 
		self.dfEdges = dict() # Stores the directed edges according to Schmidt's Algorithm.
		self.chainEdges = dict() # Store if an edge is part of a chain.
		self.bridges = []
		# Initialise variables.
		for sw in range(1, swCount + 1):
			self.visited[sw] = False
			self.dfEdges[sw] = []

		def dfs(sw) :
			self.dfSwList.append(sw) 
			self.visited[sw] = True
			for n in self.neighbours[sw] :
				# Is node visited and not parent. 
				if self.visited[n] == True: 
					pos1 = self.dfSwList.index(sw)
					pos2 = self.dfSwList.index(n)
					if not pos1 - pos2 == 1 and pos1 > pos2: 
						# Back Edge. Add directed edge n -> sw
						self.dfEdges[n].append(sw)				
				else :  
					# Node not visited. Apply DFS on child.
					dfs(n)

		dfs(1)
		# Mark all vertices as unself.visited.
		for sw in range(1, swCount + 1):
			self.visited[sw] = False

		chains = []
		#Traverse in order of DFS Tree
		for sw in self.dfSwList :
			self.visited[sw] = True
			for n in self.dfEdges[sw] : 
				key = str(sw)+"-"+str(n)
				# Back Edge. From Chain.
				chain = [sw, n]

				# Traverse back edge and back till we reach a self.visited vertex
				self.visited[n] == True

				pos = self.dfSwList.index(n) - 1
				# traverse back to root.
				while pos > -1 : 
					swChain = self.dfSwList[pos]			
					if self.visited[swChain] == False :
						chain.append(swChain)
						self.visited[swChain] = True
					elif self.visited[swChain] == True:
						# Last element of chain. 
						chain.append(swChain)
						break 
					pos -= 1

				chains.append(chain)

		# Find all edges not in any chain. Those edges are bridges.
		for chain in chains :
			i = 0
			while i < len(chain) - 1 :
				if chain[i] > chain[i+1] :
					edge = str(chain[i+1]) + "-" + str(chain[i]) 
				else :
					edge = str(chain[i]) + "-" + str(chain[i+1]) 
				self.chainEdges[edge] = True
				i += 1

		for sw in range(1, swCount + 1):
			for n in self.neighbours[sw] :
				if sw > n : continue
				else :
					edge = str(sw) + "-" + str(n)
					if not edge in self.chainEdges :
						# Edge not in chain. It is a bridge
						self.bridges.append([sw,n])

		









t = Topology("a")


