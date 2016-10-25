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
	def __init__(self, topo, pdb, pcRange, subnets) :
		self.topology = topo
		self.pdb = pdb

		swCount = self.topology.getSwitchCount()
		self.endpoints = []
		self.destinationDAGs = dict()
		self.destinationSwitches = dict()
		self.paths = dict()

		destinationSubnets = subnets

		currpc = 0
		while currpc < pcRange : 
			dst = currpc % destinationSubnets

			length = random.randint(3, self.topology.getMaxPathLength())

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


	def getDestinationDAGs(self) :
		for dst in self.destinationDAGs : 
			dag = self.destinationDAGs[dst]
			self.pdb.addDestinationDAG(dst, dag)

		return self.destinationDAGs

	def getEndpoints(self) :
		return self.endpoints

	def getPaths(self) :
		return self.paths





