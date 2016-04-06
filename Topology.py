import networkx as nx
import metis
import time
from collections import deque
import math
from Queue import PriorityQueue 
import copy

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

		self.disabledEdges = dict()

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
		elif len(self.disabledEdges) > 0 : 
			# Certain edges are disabled.
			neighbours1 = self.neighbours[swID]
			neighbours2 = []
			for n in neighbours1 : 
				key = str(swID) + "-" + str(n)
				if key not in self.disabledEdges : 
					# Edge not disabled
					neighbours2.append(n)
			return neighbours2
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
		self.edgeWeights = [[10000 for x in range(swCount + 1)] for x in range(swCount + 1)]

	def addWeight(self, sw1, sw2, ew) :
		self.edgeWeights[sw1][sw2] = ew

	def printWeights(self) :
		print "Printing Edge Weights"
		swCount = self.getSwitchCount()
		for sw in range(1, swCount + 1) :
			neighbours = self.getSwitchNeighbours(sw)
			for n in neighbours : 
				print sw, "->", n, ":", self.edgeWeights[sw][n]

	def getShortestPath(self, src, dst, routefilters=[]) :
		# Routefilters : list of edges which are disabled. Disable those edges.
		if src == dst : return [src]
		swCount = self.getSwitchCount()

		dist = dict()
		prev = dict()
		visited = dict()

		for sw in range(1, swCount + 1) :
			dist[sw] = 1000000
			prev[sw] = None
			visited[sw] = False

		dist[src] = 0
		
		while not visited[dst] :
			mindist = 1000000
			minsw = None
			for sw in range(1, swCount + 1) :
				if not visited[sw] and dist[sw] < mindist : 
					minsw = sw
					mindist = dist[sw]

			if minsw == None : 
				# no vertex remains. Thus, no path exists. 
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
		path = [dst]
		prevsw = prev[dst]

		while prevsw <> src :
			path.append(prevsw) 
			prevsw = prev[prevsw]   
		path.append(src)
		path.reverse()
		return path

	def checkUniquenessShortestPath(self, spath, routefilters) :
		""" Check if there exists a path different from spath with the same weight """
		spathWeight = 0
		i = 0
		for i in range(len(spath) - 1) : 
			spathWeight += self.edgeWeights[spath[i]][spath[i+1]]
		src = spath[0]
		dst = spath[len(spath) - 1]

		i = 0
		for i in range(len(spath) - 1) : 
			disabledEdges = copy.deepcopy(routefilters)
			disabledEdges.append([spath[i], spath[i+1]])
			path = self.getShortestPath(src, dst, disabledEdges) # Obtain the shortest path without this edge in the path.
			if len(path) == 0 : 
				# No path exists. 
				continue
			pathW = 0
			for j in range(len(path) - 1) : 
				pathW += self.edgeWeights[path[j]][path[j+1]] 

			if pathW <= spathWeight : 
				# Another shorter path exists. Violation
				return False
		return True

	def getPathDistance(self, path) :
		""" Returns the distance of path """
		i = 0
		dist = 0
		while i < len(path) - 1 :
			sw1 = path[i]
			sw2 = path[i + 1]
			dist += self.edgeWeights[sw1][sw2]
			i += 1
		return dist
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

	def enableAllEdges(self) :
		self.disabledEdges = dict()

	def disableEdge(self, sw1, sw2) : 
		""" disables directed edge sw1 -> sw2 """
		key = str(sw1) + "-" + str(sw2)
		self.disabledEdges[key] = True

	def isSwitchDisabled(self, sw) :
		neighbours = self.neighbours[sw]
		isDisabled = True
		for n in neighbours :
			key1 = str(sw) + "-" + str(n)
			key2 = str(n) + "-" + str(sw)
			if key1 not in self.disabledEdges or key2 not in self.disabledEdges: 
				isDisabled = False
		return isDisabled

	def isConnected(self, src, dst, mid=None) :
		""" Is there a path from src to dst which passes through mid """
		if src == dst and sw <> None : return False # Weird case, shouldnt arise. 

		visited = dict()
		for sw in range(1, self.getSwitchCount()+1) :
			visited[sw] = False

		if mid <> None : 
			# BFS from src to mid and then bfs from mid to dst
			swQueue1 = [src]
			swQueue2 = []
			midReach = False
			while len(swQueue1) > 0 and not midReach:
				for sw in swQueue1 : 
					visited[sw] = True
					neighbours = self.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n == mid : midReach = True
						elif n not in swQueue2 and not visited[n]: swQueue2.append(n)
				swQueue1 = swQueue2 
				swQueue2 = []

			if not midReach : return False # src -> mid not connected.

			for sw in range(1, self.getSwitchCount() + 1) :
				visited[sw] = False

			# BFS from mid to dst
			swQueue1 = [mid]
			swQueue2 = []
			dstReach = False
			while len(swQueue1) > 0 and not dstReach:
				for sw in swQueue1 : 
					visited[sw] = True
					neighbours = self.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n == dst : dstReach = False
						elif n not in swQueue2 and not visited[n]: swQueue2.append(n)
				swQueue1 = swQueue2 
				swQueue2 = []
			return dstReach
		else : 
			# BFS from src to dst
			swQueue1 = [src]
			swQueue2 = []
			dstReach = False
			while len(swQueue1) > 0 and not dstReach:
				for sw in swQueue1 : 
					visited[sw] = True
					neighbours = self.getSwitchNeighbours(sw)
					for n in neighbours : 
						if n == mid : dstReach = True
						elif n not in swQueue2 and not visited[n]: swQueue2.append(n)
				swQueue1 = swQueue2 
				swQueue2 = []

			return dstReach
		


		





