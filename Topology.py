import networkx as nx
import metis
import time
from collections import deque
import math
from Queue import PriorityQueue 

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

		# Tactic variable.
		self.switchLabels = dict()

		self.useTopologySlicingFlag = False
		self.useBridgeSlicing = False


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

	def getSwitchNeighbours(self, swID, bridgeSlicing=False) :
		if bridgeSlicing and self.useBridgeSlicing and swID in self.bridgeSliceMap: 
			slice = self.bridgeSliceMap[swID]
			neighbours = self.neighbours[swID] 
			sliceNeighbours = []
			for n in neighbours : 
				if n in self.bridgeSliceMap and slice == self.bridgeSliceMap[n] :
					sliceNeighbours.append(n)
			return sliceNeighbours
		elif self.useTopologySlicingFlag : 
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
		self.backEdges = dict()
		self.chainEdges = dict() # Store if an edge is part of a chain.
		self.bridges = []
		# Initialise variables.
		for sw in range(1, swCount + 1):
			self.visited[sw] = False
			self.dfEdges[sw] = []
			self.backEdges[sw] = []

		def dfs(sw, parent) :
			self.dfSwList.append(sw) 
			self.visited[sw] = True
			if parent <> None : 
				self.dfEdges[sw].append(parent)

			for n in self.neighbours[sw] :
				# Is node visited and not parent. 
				if self.visited[n] == True: 
					pos1 = self.dfSwList.index(sw)
					pos2 = self.dfSwList.index(n)
					if n <> parent and pos2 < pos1: 
						# Back Edge. Add directed edge n -> sw
						self.backEdges[n].append(sw)            
				else :  
					# Node not visited. Apply DFS on child.
					dfs(n, sw)

		dfs(1, None)
		# Mark all vertices as unself.visited.
		for sw in range(1, swCount + 1):
			self.visited[sw] = False

		chains = []
		#Traverse in order of DFS Tree
		for sw in self.dfSwList :
			self.visited[sw] = True
			for n in self.backEdges[sw] : 
				key = str(sw)+"-"+str(n)

				# Back Edge. From Chain.
				chain = [sw, n]

				
				if self.visited[n] == False : 
					# Traverse back edge and back till we reach a self.visited vertex
					self.visited[n] = True

					parent = self.dfEdges[n][0]
					# traverse back to root.
					while True :            
						if self.visited[parent] == False :
							chain.append(parent)
							self.visited[parent] = True
							parent = self.dfEdges[parent][0]
						elif self.visited[parent] == True:
							# Last element of chain. 
							chain.append(parent)
							break 

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

		if len(self.bridges) > 0 : 
			# bridges exist, set useBridgeSlicing
			self.useBridgeSlicing = True
			
		# Allot slices.
		slice = 0
		self.bridgeSliceMap = dict()
		for chain in chains:
			noSliceFlag = True
			chainSlice = None
			for sw in chain :
				if sw in self.bridgeSliceMap :
					chainSlice = self.bridgeSliceMap[sw]
					noSliceFlag = False
			if noSliceFlag == False : 
				# Chain part of existing slice.
				for sw in chain :
					self.bridgeSliceMap[sw] = chainSlice
			else :
				# Allocate new slice
				for sw in chain :
					self.bridgeSliceMap[sw] = slice
				slice += 1

		self.bridgeSlices = dict()
		for sw in self.bridgeSliceMap.keys() : 
			slice = self.bridgeSliceMap[sw]
			if slice not in self.bridgeSlices : 
				self.bridgeSlices[slice] = [sw]
			else :
				self.bridgeSlices[slice].append(sw)

		return self.useBridgeSlicing

	def getBridgeSlice(self, slice) :
		if slice in self.bridgeSlices :  
			return self.bridgeSlices[slice]
		else :
			return []

	def getBridgeSliceNumber(self, sw):
		""" returns the bridge slice number"""
		if sw in self.bridgeSliceMap : 
			return self.bridgeSliceMap[sw]
		else :
			return None

	def getDistance(self, sw1, sw2) :
		""" returns number of edges in shortest path from sw1 to sw2 """
		if sw1 == sw2 : return 0

		level = 0
		swQueue1 = [sw1]
		swQueue2 = []

		while len(swQueue1) > 0 :
			level += 1
			for sw in swQueue1 : 
				neighbours = self.getSwitchNeighbours(sw)
				for n in neighbours : 
					if n == sw2 : return level
					elif n not in swQueue2 : swQueue2.append(n)
			swQueue1 = swQueue2 
			swQueue2 = []

	def initializeWeights(self) :
		# Edge Weights
		swCount = self.getSwitchCount()
		self.edgeWeights = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]

	def addWeight(self, sw1, sw2, ew) :
		self.edgeWeights[sw1][sw2] = ew

	def getShortestPath(self, sw1, sw2, routefilters=None) :
		# Routefilters : list of edges which are disabled. Disable those edges.
		if sw1 == sw2 : return [sw1]
		swCount = self.getSwitchCount()

		dist = dict()
		prev = dict()
		visited = dict()

		for sw in range(1, swCount + 1) :
			dist[sw] = 1000000
			prev[sw] = None
			visited[sw] = False

		dist[sw1] = 0
		
		while not visited[sw2] :
			mindist = 1000000
			minsw = None
			for sw in range(1, swCount + 1) :
				if not visited[sw] and dist[sw] < mindist : 
					minsw = sw
					mindist = dist[sw]

			if minsw == None : 
				# vertex remains. Thus, no path exists. 
				return []
			visited[minsw] = True
			neighbours = self.getSwitchNeighbours(minsw)

			for n in neighbours :
				# Route filter present for edge, do not consider the edge.
				if [minsw, n] in routefilters : continue 
				if not visited[n] :
					alt = dist[minsw] + float(self.edgeWeights[minsw][n])
					if alt < dist[n] : 
						dist[n] = alt
						prev[n] = minsw

		# Backtrack to find source
		path = [sw2]
		prevsw = prev[sw2]

		while prevsw <> sw1 :
			path.append(prevsw) 
			prevsw = prev[prevsw]   
		path.append(sw1)
		path.reverse()
		return path

	def getAllPaths(self, src, dst, routefilters=None) :
		""" Returns all edge-disjoint paths and costs from src to dst """
		paths = []
		path = self.getShortestPath(src, dst, routefilters)
		while path <> [] :
			paths.append(path)
			for i in range(len(path) - 1) : 
				# Disable all edges from the path
				routefilters.append([path[i], path[i+1]])
				# compute next path
			path = self.getShortestPath(src, dst, routefilters)

		return paths

	def useTopologySlicing(self) :
		self.useTopologySlicingFlag = True

	def resetTopologySlicing(self) :
		self.useTopologySlicingFlag = False

	def createSliceGraph(self):
		""" Creates the slice graph of the topology. Each slice is represented 
		by a single node and slices are connected by a single edge if there exists 
		a non-zero number of inter-slice edges"""

		(edgecuts, partitions) = metis.part_graph(graph=self.graph, nparts=5, contig=True)
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
		print "SliceEdges", slice1, slice2, sliceEdges
		return sliceEdges

	def getSliceGraph(self) :
		""" Return slice graph in terms of [slice, edgeKey-list] for each slice to 
		initialize the Slice Graph Solver"""

		sliceGraph = []
		for slice1 in self.slices : 
			sliceEdgeKeys = []
			for slice2 in self.slices : 
				if slice1 == slice2 : continue
				sliceEdges = self.getSliceEdges(slice1, slice2)
				for edge in sliceEdges : 
					if edge[0] < edge[1] :
						sliceEdgeKeys.append(str(edge[0]) + "-" + str(edge[1]))
					else : 
						sliceEdgeKeys.append(str(edge[1]) + "-" + str(edge[0]))
			sliceGraph.append([slice1, sliceEdgeKeys])

		return sliceGraph

	def printSwitchMappings(self) :
		self.networkDatabase.printSwitchMappings() 

	def validatePath(self, path) :
		""" checks if the path is a valid path in the topology"""
		i = 0
		while i < len(path) - 1:
			neighbours = self.neighbours[path[i]]
			if path[i+1] not in neighbours :
				print "pathi", self.getSwName(path[i]), self.getSwName(path[i+1])
				return False
			i += 1
		return True

	def findPathCount(self, src, dst) :
		srcSw = self.getSwID(src)
		dstSw = self.getSwID(dst)

		return len(list(nx.all_simple_paths(self.graph, source=srcSw, target=dstSw, cutoff=self.getMaxPathLength())))

	def assignLabels(self) :
		""" Currently for fattrees """
		self.labelSet = ["a", "c", "e"]
		swCount = self.getSwitchCount()
		for sw in range(1, swCount+1) :
			swName = self.getSwName(sw)
			self.switchLabels[sw] = swName[0]

		self.labelneighbours = dict()
		for label in self.labelSet : 
			self.labelneighbours[label] = []

		# Build Label adjacency matrix.
		for sw in range(1, swCount+1) :
			label = self.switchLabels[sw]
			neighbours = self.neighbours[sw]
			for n in neighbours :
				nlabel = self.switchLabels[n]
				if nlabel not in self.labelneighbours[label]:
					self.labelneighbours[label].append(nlabel)

	def getLabel(self, sw) :
		return self.switchLabels[sw]

	def isLabelConnected(self, label1, label2):
		""" Returns true if labels are connected """
		return label1 in self.labelneighbours[label2]






