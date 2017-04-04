import networkx as nx
#import metis
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

	def getAllSwitchNeighbours(self, swID) :
		"""Returns all enabled/disabled edges neighbours  """
		return self.neighbours[swID]

	def getNeighbours(self) :
		return self.neighbours

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
				# Route filter present for edge, do not consider the edges
				if [minsw, n] in routefilters : 
					continue 
				elif not visited[n] :
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

	def getAllShortestPaths(self, src, dst, routefilters=[]) :
		# Routefilters : list of edges which are disabled. Disable those edges.
		# Return all equidistant shortest paths from src to dst.
		if src == dst : return [src]
		path = self.getShortestPath(src, dst, routefilters)
		if len(path) == 0 : 
			return []
		distance = self.getPathDistance(path)
		paths = [path]
		while len(path) > 0 : 
			routefilters.append([path[0], path[1]])
			
			path = self.getShortestPath(src, dst, routefilters)
			if self.getPathDistance(path) == distance : 
				paths.append(path)
			else :
				path = []

		return paths

	def getShortestPathStaticRoutes(self, srcSw, dstSw, staticRoutes, disabledEdges=[]) :
		nextsw = srcSw
		path = [srcSw]
		while nextsw != dstSw :
			staticnexthop = False 
			for sr in staticRoutes : 
				if sr[0] == nextsw and sr not in disabledEdges : 
					nextsw = sr[1]
					staticnexthop = True
					break

			if not staticnexthop :
				spath = self.getShortestPath(nextsw, dstSw, disabledEdges) 
				if len(spath) == 0 : 
					print "no path found"
					return []
				
				nextsw = spath[1]

			if nextsw in path : 
				# Static route causes loop under failure
				print path, nextsw
				print "Looping path"
				return []
			
			path.append(nextsw)
		
		return path

	# def checkConnectivityStaticRoutes(self, srcSw, dstSw, staticRoutes, disabledEdges=[]) :
	# 	nextsw = []
	# 	path = [srcSw]
		
	# 	staticnexthop = False 
	# 	for sr in staticRoutes : 
	# 		if sr[0] == srcSw and sr not in disabledEdges : 
	# 			nextsw.append(sr[1])		
					

	# 	if len(nextsw) > 0 :
	# 		# Static routes exist at switch
	# 		for n in nextsw : 
	# 			stat = self.checkConnectivityStaticRoutes(n, dstSw, staticRoutes, disabledEdges)

	# 		spaths = self.getAllShortestPaths(srcSw, dstSw, disabledEdges) 
	# 		if len(spath) == 0 : 
	# 			print "no path found"
	# 			return []
			
		

	# 	if nextsw in path : 
	# 		# Static route causes loop under failure
	# 		print path, nextsw
	# 		print "Looping path"
	# 		return []
		
	# 	path.append(nextsw)
		
	# 	return path

	def checkRoutingLoop(self, srcSw, dstSw, staticRoutes, disabledEdges=[]) :
		nextsw = srcSw
		path = [srcSw]
		while nextsw != dstSw :
			staticnexthop = False 
			for sr in staticRoutes : 
				if sr[0] == nextsw and sr not in disabledEdges : 
					nextsw = sr[1]
					staticnexthop = True
					break

			if not staticnexthop :
				spath = self.getShortestPath(nextsw, dstSw, disabledEdges) 
				if len(spath) == 0 :
					return True
				nextsw = spath[1]

			if nextsw in path : 
				# Static route causes loop under failure
				return False
			
			path.append(nextsw)
		
		return True

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
		if len(path) == 0 :
			return 1000000000

		i = 0
		dist = 0
		while i < len(path) - 1 :
			sw1 = path[i]
			sw2 = path[i + 1]
			dist += self.edgeWeights[sw1][sw2]
			i += 1
		return dist

	def getAllPaths(self, src, dst, routefilters=[]) :
		""" Returns all edge-disjoint paths and costs from src to dst """
		paths = []
		path = self.getShortestPath(src, dst, routefilters)
		while path != [] :
			paths.append(path)
			for i in range(len(path) - 1) : 
				# Disable all edges from the path
				routefilters.append([path[i], path[i+1]])
				# compute next path
			path = self.getShortestPath(src, dst, routefilters)
		return paths

	def checkResilience(self, src, dst, t_res, routefilters) :
		paths = self.getAllPaths(src, dst, routefilters)
		if len(paths) >= t_res + 1 :
			return True
		else : 
			return False

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

	def findMinCut(self, srcSw, dstSw, disabledEdges=[]) :
		# finds the minimum cut from srcSw to dstSw with disabled filters 
		dEdges = copy.deepcopy(disabledEdges)

		visited = dict()
		bfstree = dict()
		queue1 = [srcSw]

		while len(queue1) != 0:
			sw = queue1.pop(0)
			visited[sw] = True
			if sw == dstSw : 
				# Found shortest path from srcSw to dstSw. Remove and check. 
				sw1 = dstSw 
				while sw1 != srcSw:
					edge = [bfstree[sw1], sw1]
					dEdges.append(edge)
					sw1 = bfstree[sw1]

				return 1 + self.findMinCut(srcSw, dstSw, dEdges)
			else :
				neighbours = self.getAllSwitchNeighbours(sw)
				for n in neighbours :
					if [sw,n] in dEdges : continue # Filtered. Dont explore.
					elif n in visited : continue # Switch already visited
					else : 
						if n not in queue1 : 
							queue1.append(n)
							bfstree[n] = sw

		return 0
		
	def getBFSPath(self, srcSw, dstSw, disabledEdges=[]):
		bfstree = dict()
		visited = dict()

		if srcSw == dstSw : 
			return [srcSw]

		swQueue = deque([srcSw])
		while len(swQueue) > 0 :
			sw = swQueue.popleft()
			visited[sw] = True
			if sw == dstSw :
				path = [dstSw]
				nextsw = bfstree[dstSw]
				while nextsw <> srcSw :
					path.append(nextsw)
					nextsw = bfstree[nextsw]
				path.append(srcSw)
				# Reverse path.
				path.reverse()

				return path

			neighbours = self.getSwitchNeighbours(sw)
			for n in neighbours : 
				if n not in visited and [sw, n] not in disabledEdges :
					bfstree[n] = sw
					swQueue.append(n)

		return []

	def checkTopologyContinuity(self) : 
		""" Check if all switches in the topology are connected"""
		reachableSwitches = dict()
		swCount = self.getSwitchCount()
		reachableSwitches[1] = True
		switchQueue = [1]

		while len(reachableSwitches) < swCount:
			if len(switchQueue) == 0 : 
				# Partition in domain. Not valid! 
				return False
			sw = switchQueue.pop(0)
			neighbours = self.getSwitchNeighbours(sw)
			for n in neighbours :
				if n not in reachableSwitches and n not in switchQueue: 
					reachableSwitches[n] = True
					switchQueue.append(n)	

		return True





