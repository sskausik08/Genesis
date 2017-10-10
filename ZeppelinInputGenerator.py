from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import networkx as nx
import copy
import math


""" Generating random dags for Zeppelin """

class ZeppelinInputGenerator(object) :
	def __init__(self, topo, pdb, pcRange, subnets, distance) :
		self.topology = topo
		self.pdb = pdb

		swCount = self.topology.getSwitchCount()
		self.endpoints = []
		self.destinationDAGs = dict()
		self.destinationSwitches = dict()
		self.paths = dict()
		self.backupPaths = dict()

		destinationSubnets = subnets

		currpc = 0
		while currpc < pcRange : 
			dst = currpc % destinationSubnets

			length = random.randint(3, distance)

			if dst not in self.destinationDAGs : 
				self.destinationDAGs[dst] = dict()
				dstSw = random.randint(1, swCount)
				self.destinationDAGs[dst][dstSw] = None
				self.destinationSwitches[dst] = dstSw
			dag = self.destinationDAGs[dst]
			dstSw = self.destinationSwitches[dst]

			# Do a random DFS from dst to length steps
			diverged = False
			depth = 0
			sw = dstSw
			while depth < length:
				neighbours = self.topology.getSwitchNeighbours(sw)
				while True : 
					nextsw = neighbours[random.randint(0, len(neighbours) - 1)]
					if not diverged : 
						# sw is in dag. Any switch which isnt connected in dag to another switch is
						if nextsw not in dag or dag[nextsw] == sw :
							break
						else : 
							count = 0
							for n in neighbours :
								if n not in dag or dag[n] == sw : 
									count += 1
							if count == 0 : 
								# Cannot proceed. Exit with here. 
								nextsw = None 
								break

					else :
						# path has diverged from dag. Dont intersect with dag again
						if nextsw not in dag : 
							break
						else :
							# Check if any neighbours is not in dag
							count = 0
							for n in neighbours :
								if n not in dag : 
									count += 1
							if count == 0 : 
								# Cannot proceed. Exit with here. 
								nextsw = None 
								break

				# Cannot proceed with DFS. exit.
				if nextsw == None :
					break
				else :
					if nextsw not in dag : 
						diverged = True
						# add nextsw to dag
						dag[nextsw] = sw
					sw = nextsw
					depth += 1

			if depth > 0 : 
				# sw ->  dstSw is a valid path
				path = []
				nextsw = sw
				while nextsw <> dstSw :
					path.append(nextsw)
					nextsw = dag[nextsw]
				path.append(nextsw)
				if len(path) <= 1: 
					print "Some error!"
					exit(0)

				if [sw, dst] in self.endpoints :
					continue
					
				self.endpoints.append([sw, dst])
				pc = self.pdb.addReachabilityPolicy(dst, sw, dstSw)
				self.pdb.addPath(pc, path)
				self.paths[pc] = path

				currpc += 1

		currpc = 0
		while currpc < pcRange : 
			dst =  currpc % destinationSubnets
			backupPath = self.getBackupPath(currpc, dst)
			if len(backupPath) > 0 :
				if dst not in self.backupPaths : 
					self.backupPaths[dst] = [backupPath]	
				else : 
					self.backupPaths[dst].append(backupPath)		
			currpc += 1


	def getBackupPath(self, pc, dst): 
		swCount = self.topology.getSwitchCount()

		# Find backup path for pc=0
		origPath = self.paths[pc] 
		startSw = origPath[0]
		dstSw = origPath[len(origPath) - 1]
		dag = self.destinationDAGs[dst]
		visited = dict()
		prev = dict()
		# Do a BFS from startSw to dstSw which does not intersect dag
		swQueue = [startSw]
		prev[startSw] = None
		while len(swQueue) > 0 :
			currSw = swQueue.pop(0)
			visited[currSw] = True
			neighbours = self.topology.getSwitchNeighbours(currSw)
			for n in neighbours : 
				if n == dstSw : 
					# Reached destination. Extract path
					backupPath = [dstSw]
					while currSw != None:
						backupPath.append(currSw)
						currSw = prev[currSw]
					backupPath.reverse()
					if len(backupPath) == 2 and dag[backupPath[0]] == backupPath[1]: 
						# [startSw, dstSw] dont accept
						continue
					return backupPath
				elif n in visited or n in dag : 
					continue
				elif n not in swQueue : 
					prev[n] = currSw
					swQueue.append(n)

		return []

	def getDestinationDAGs(self) :
		for dst in self.destinationDAGs : 
			dag = self.destinationDAGs[dst]
			self.pdb.addDestinationDAG(dst, dag)

		return self.destinationDAGs

	def getEndpoints(self) :
		return self.endpoints

	def getPaths(self) :
		return self.paths

	def getBackupPaths(self) :
		return self.backupPaths

	def getStaticRoutes(self) :
		return None





