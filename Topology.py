import networkx as nx
import metis
import time


class NetworkDatabase(object) :
	""" Database to store the switch mappings to integers """

	def __init__(self) :
		self.switchMap = ["dropSwitch"]
		self.swID = 1

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
			if i == 0 : 
				i += 1 
				continue
			print sw, ":", i
			i += 1

class Topology(object):
	"Class for a Topology"
	def __init__(self, name="topo-0"):
		self.name = name
		self.networkDatabase = NetworkDatabase()
		self.neighbours = dict()
		
		# Topology Slicing variables.
		self.slices = dict() # Stores the switches in every slice.
		self.switchSliceMap = dict()  # Stores the slice number for each switch.
		self.graph = nx.Graph()
		self.sliceGraph = nx.Graph()
		self.maxPathLength = 10

		self.useTopologySlicingFlag = False

	def getName(self) :
		return self.name

	def addSwitch(self, name, neighbours) :
		if not self.networkDatabase.existsSwitch(name):
			swID = self.networkDatabase.insertSwitch(name)
			self.neighbours[swID] = []
			self.graph.add_node(swID, switch=str(swID))
		else :
			swID = self.networkDatabase.getSwID(name)

		for n in neighbours :
			if not self.networkDatabase.existsSwitch(n) :
				nID = self.networkDatabase.insertSwitch(n)
				self.neighbours[nID] = []
				self.graph.add_node(nID, switch=str(nID))
			else :
				nID = self.networkDatabase.getSwID(n)

			self.graph.add_edge(swID, nID)
			if not nID in self.neighbours[swID] :
				self.neighbours[swID].append(nID)
			if not swID in self.neighbours[nID] :
				self.neighbours[nID].append(swID)

	def getSwID(self, swName) :
		return self.networkDatabase.getSwID(swName)

	def getSwName(self, swID) :
		return self.networkDatabase.getSwitchName(swID)

	def getMaxPathLength(self) :
		return self.maxPathLength

	def setMaxPathLength(self, pathlen):
		self.maxPathLength = pathlen
		
	def getSwitchCount(self) :
		return self.networkDatabase.getSwitchCount() - 1

	def getSwitchNeighbours(self, swID) :
		if self.useTopologySlicingFlag : 
			# Find the neighbours in the slice. 
			slice = self.getSliceNumber(swID)
			neighbours = self.neighbours[swID] 
			sliceNeighbours = []
			for n in neighbours : 
				if n in self.slices[slice] :
					sliceNeighbours.append(n)
			return sliceNeighbours
		else :
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

	def useTopologySlicing(self) :
		self.useTopologySlicingFlag = True

	def createSliceGraph(self):
		""" Creates the slice graph of the topology. Each slice is represented 
		by a single node and slices are connected by a single edge if there exists 
		a non-zero number of inter-slice edges"""

		# Test Slice. Topo is slice.topo
		# self.setSlice(1,0)
		# self.setSlice(2,0)
		# self.setSlice(3,0)
		# self.setSlice(5,1)
		# self.setSlice(6,1)
		# self.setSlice(8,1)
		# self.setSlice(4,2)
		# self.setSlice(7,2)
		# self.setSlice(9,2)
		# self.setSlice(10,3)
		# self.setSlice(11,3)
		print nx.minimum_edge_cut(self.graph)
		(edgecuts, partitions) = metis.part_graph(graph=self.graph, nparts=10, contig=True)
		i = 0	
		for node in self.graph.nodes():
			sw = int(node)

			# Set slice number. 
			self.setSlice(sw, partitions[i])
			print "Slice mapping",sw,partitions[i] 
			i += 1


		for slice in self.slices.keys() : 
			self.sliceGraph.add_node(slice, slice=str(slice))

		for slice in self.slices.keys():
			swList = self.slices[slice]

			for sw in swList :
				neighbours = self.neighbours[sw]
				for n in neighbours :
					slice2 = self.switchSliceMap[n]
					if slice == slice2 : continue
					elif self.sliceGraph.has_edge(slice, slice2) : continue
					else : self.sliceGraph.add_edge(slice, slice2)

		
	def setSlice(self, sw, slice) :
		if slice in self.slices : 
			if not sw in self.slices[slice] :
				self.slices[slice].append(sw)
				self.switchSliceMap[sw] = slice
		else :
			self.slices[slice] = [sw]
			self.switchSliceMap[sw] = slice
		
	def getSliceNumber(self, sw):
		""" returns the topology slice number"""
		return self.switchSliceMap[sw]

	def getTopologySlice(self, slice) :
		if slice in self.slices :  
			return self.slices[slice]
		else :
			return []

	def getSliceGraphPaths(self, slice1, slice2, sliceWaypoints=None) :
		st = time.time()
		allpaths = nx.all_simple_paths(self.sliceGraph, source=slice1, target=slice2)
		et = time.time() - st
		validpaths = []
		if sliceWaypoints == None : 
			return allpaths

		# Slice Waypoints.
		for path in allpaths : 
			valid = True
			for slice in sliceWaypoints : 
				valid = valid and (slice in path) 
			if valid :
				validpaths.append(path) 
		
		return validpaths

	def getSliceEdges(self, slice1, slice2) :
		swList1 = self.slices[slice1]
		swList2 = self.slices[slice2]
		sliceEdges = []
		for sw in swList1 : 
			neighbours = self.neighbours[sw]
			for n in neighbours : 
				if n in swList2 :
					sliceEdges.append([sw,n])
		return sliceEdges

	def getSliceGraph(self) :
		""" Return slice graph in terms of [slice, edgeKey-list] for each slice to 
		initialize the Slice Graph Solver"""

		sliceGraph = []
		for slice1 in self.slices : 
			sliceEdgeKeys = []
			for slice2 in self.slices : 
				sliceEdges = self.getSliceEdges(slice1, slice2)
				for edge in sliceEdges : 
					if edge[0] < edge[1] :
						sliceEdgeKeys.append(str(edge[0]) + "-" + str(edge[1]))
					else : 
						sliceEdgeKeys.append(str(edge[1]) + "-" + str(edge[0]))
			sliceGraph.append([slice, sliceEdgeKeys])

		return sliceGraph

	def printSwitchMappings(self) :
		self.networkDatabase.printSwitchMappings() 

	def validatePath(self, path) :
		""" checks if the path is a valid path in the topology"""
		i = 0
		while i < len(path) - 1:
			neighbours = self.getSwitchNeighbours(path[i])
			if path[i+1] not in neighbours :
				return False
			i += 1
		return True









t = Topology("a")


