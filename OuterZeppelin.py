from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx
from subprocess import *
from collections import deque
import math
import gurobipy as gb
import copy
from collections import defaultdict



class OuterZeppelin(object) :
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



	def calculateLocalPreferences(self) : 
		dsts = self.pdb.getDestinations() 
		return 5;

	def metropolisWalk(self, numDomains) :
		# Start a MCMC sampling walk with number of domains=numDomains. 


	def randomDomainAssignment(self, numDomains):
		""" Generate a random domain assignment to start the Metropolis walk"""

		swCount = self.topology.getSwitchCount()
		domainSize = swCount / numDomains # We divide the routers equally across the domains

		for sw in range(1, swCount + 1) :
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
					# No neighbour assigned. Randomly assign a domain to this switch
					self.switchDomains[sw] = random.randint(0, numDomains - 1)
				elif len(neighbouringDomains.keys()) == 1 and not unassignedNeighbour:
					# All neighbours are assigned to same domain, assign this to same domain
					self.switchDomains[sw] = self.switchDomains[neighbours[0]]
				else : 
					# Some neighbours are assigned, some are not. 
					# Pick one of the domains, or a new one by random.











		





