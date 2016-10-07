from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import networkx as nx
from subprocess import *
from collections import deque
import math
import copy
from collections import defaultdict

class OuterZeppelinSynthesiser(object) :
	def __init__(self, topology, pdb) :
		self.topology = topology
		self.pdb = pdb
 	
 		# Store switch domains for each switch
		self.switchDomains = dict()

		self.domainUpperLimit = 20
		self.domainLowerLimit = 5

	def enforceDAGs(self, dags, endpoints):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.endpoints = copy.deepcopy(endpoints)

		start_t = time.time() 

		self.randomDomainAssignment(5)

	def calculateLocalPreferences(self) : 
		dsts = self.pdb.getDestinations() 
		return 5;

	def metropolisWalk(self, numDomains) :
		# Start a MCMC sampling walk with number of domains=numDomains. 
		pass

	def randomDomainAssignment(self, numDomains):
		""" Generate a random domain assignment to start the Metropolis walk"""

		swCount = self.topology.getSwitchCount()
		domainSize = swCount / numDomains # We divide the routers equally across the domains

		switches = range(1, swCount + 1)

		currDomain = 0

		while len(self.switchDomains) != swCount:
			random.shuffle(switches)
		 	for sw in switches :
				if sw in self.switchDomains and self.switchDomains[sw] > -1 :
					# Switch assigned. 
					continue
				else : 
					# Switch not assigned.
					neighbours = self.topology.getSwitchNeighbours(sw)
					neighbouringDomains = dict()
					unassignedNeighbour = False
					for n in neighbours : 
						if n in self.switchDomains and self.switchDomains[n] > -1 :
							# Neighbour assigned
							neighbouringDomains[self.switchDomains[n]] = True
						else : 
							unassignedNeighbour = True

					if len(neighbouringDomains.keys()) == 0 : 
						# No neighbour assigned. Assign a new domain to this switch
						if currDomain >= numDomains : continue
						self.switchDomains[sw] = currDomain 
						currDomain += 1

					elif len(neighbouringDomains.keys()) == 1 and not unassignedNeighbour:
						# All neighbours are assigned to same domain, assign this to same domain
						self.switchDomains[sw] = self.switchDomains[neighbours[0]]
					else : 
						# Some neighbours are assigned, some are not. 
						# Pick one of the domains, or a new one by random
						totalNeighbourDomains = len(neighbouringDomains.keys())
						self.switchDomains[sw] = neighbouringDomains.keys()[random.randint(0, totalNeighbourDomains - 1)]

						# assignedDomain = -1
						# for domain in neighbouringDomains.keys() : 
						# 	if random.randint(0, totalNeighbourDomains - 1) == i : 
						# 		self.switchDomains[sw] = domain
						# 		assignedDomain = domain
						# 		break
						# 	i += 1
						# if assignedDomain == -1 :
						# 	if unassignedNeighbour and len(neighbouringDomains.keys()) <= 1: 
						# 		# Assign a random domain
						# 		self.switchDomains[sw] = random.randint(0, numDomains - 1)
						# 	else : 
						# 		# Assign one neighbour's domain by random.
						# 		self.switchDomains[sw] = self.switchDomains[neighbours[random.randint(0, len(neighbours) - 1)]]

		print self.switchDomains
		# Check validity
		print "Validity ", self.checkValidDomainAssignment()

	def checkValidDomainAssignment(self) :	
		# Checks the validity of a particular domain assignment. 
		swCount = self.topology.getSwitchCount()

		for sw in range(1, swCount + 1) :
			# A switch must be connected to atleast one switch of the same domain. (Assuming no single switch domains)
			neighbours = self.topology.getSwitchNeighbours(sw)
			isConnected = False
			for n in neighbours : 
				if self.switchDomains[sw] == self.switchDomains[n] :
					isConnected = True
			if not isConnected :
				# No neighbour in same domain. Not a valid assignment
				print sw, self.switchDomains[sw], neighbours
				return False

		return True	




















		





