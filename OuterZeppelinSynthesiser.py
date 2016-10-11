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
		self.domains = dict()
		self.boundarySwitches = dict()

		self.domainUpperLimit = 20
		self.domainLowerLimit = 5

		# MCMC variables 
		self.MCMC_MAX_ITER = 5000  
		self.beta = 1.00 # Constant

	def enforceDAGs(self, dags, endpoints, numDomains=5):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.endpoints = copy.deepcopy(endpoints)
		self.numDomains = numDomains

		start_t = time.time() 

		self.MCMCWalk()

	def calculateLocalPreferences(self) : 
		dsts = self.pdb.getDestinations() 
		return 5;

	def MCMCWalk(self) :
		# Start a MCMC sampling walk with number of domains=self.numDomains. 
		
		iteration = 0
		
		# MCMC Algorithm initial step: start with a preliminary domain assignment (chosen at random)
		self.computeRandomDomainAssignment()
		self.computeBoundaries() # boundary bookkeeping for efficiency

		# Perform the Metropolis walk using the score functions. 
		# We consider solutions with a smaller score to be better. 
		for iteration in range(self.MCMC_MAX_ITER):
			oldScore = self.computeDomainAssignmentScore()

			change = self.giveRandomDomainChange()
			# Make the random change to domain assignment.
			sw = change[0]
			oldDomain = self.switchDomains[sw]
			newDomain = change[1]
			self.switchDomains[sw] = newDomain 

			# Compute new score. 
			newScore = self.computeDomainAssignmentScore()

			transitionProbability = math.exp(- self.beta * float(newScore)/float(oldScore))

			# if transitionProbability >= 1:
			# 	# Surely transition to new state
			# 	print "Score", oldScore, newScore, " Accept"
			# 	continue
			# else:
			transition = self.flip(transitionProbability) 
			if transition :	
				# accept transition to new state
				print "Score", oldScore, newScore, " Accept"

				# recompute boundaries
				self.recomputeBoundaries(sw, oldDomain, newDomain)
				continue
			else :
				# Do not transition. Revert back change.
				print "Score", oldScore, newScore, " Reject"
				self.switchDomains[sw] = oldDomain


	def flip(self, p):
		# random.random() returns a uniformly distributed pseudo-random floating point number in the range [0, 1). 
		# This number is less than a given number p in the range [0,1) with probability p. 
		return (random.random() < p) 
	
	def giveRandomDomainChange(self) :
		""" Returns a random change of domain for a boundary switch"""
		swCount = self.topology.getSwitchCount()
		
		iteration = 0
		iterationCount = 5000 # Not assigned based on anything! 

		for iteration in range(iterationCount) : 
			sw = random.randint(1, swCount) 
			domain = self.switchDomains[sw]
			
			if sw not in self.boundarySwitches[domain] : 
				# sw not a boundary switch, can't change its domain.
				continue
			else : 
				# sw is a boundary switch. 
				neighbours = self.topology.getSwitchNeighbours(sw)
				neighbouringDomains = []
				for n in neighbours : 
					ndomain = self.switchDomains[n]
					if ndomain != domain and ndomain not in neighbouringDomains : 
						neighbouringDomains.append(ndomain) 

				# pick one neighbouring domain by random and change sw's domain
				newDomain = neighbouringDomains[random.randint(0, len(neighbouringDomains) - 1)]
				# Return the random domain change picked. 
				return [sw, newDomain] 


	def computeBoundaries(self) : 
		""" Computes the boundaries of the domains"""

		swCount = self.topology.getSwitchCount()
		for sw in range(1, swCount + 1) :
			neighbours = self.topology.getSwitchNeighbours(sw)
			for n in neighbours : 
				if self.switchDomains[sw] != self.switchDomains[n] :
					# Boundary
					if self.switchDomains[sw] not in self.boundarySwitches :
						self.boundarySwitches[self.switchDomains[sw]] = [sw]
					else : 
						self.boundarySwitches[self.switchDomains[sw]].append(sw)
					break

		print self.boundarySwitches

	def recomputeBoundaries(self, sw, oldDomain, newDomain):
		""" Recompute boundaries for change"""

		self.boundarySwitches[oldDomain].remove(sw)
		self.boundarySwitches[newDomain].append(sw)

		neighbours = self.topology.getSwitchNeighbours(sw)

		for n in neighbours : 
			# Recompute boundaries for neighbours
			if self.isBoundarySwitch(n) : 
				if n not in self.boundarySwitches[self.switchDomains[n]] :
					self.boundarySwitches[self.switchDomains[n]].append(n)
			else :
				if n in self.boundarySwitches[self.switchDomains[n]] :
					self.boundarySwitches[self.switchDomains[n]].remove(n)
		

	def isBoundarySwitch(self, sw): 
		""" Returns if sw is a boundary switch or not"""
		neighbours = self.topology.getSwitchNeighbours(sw)
		for n in neighbours : 
			if self.switchDomains[sw] != self.switchDomains[n] :
				return True

		return False

	def computeRandomDomainAssignment(self):
		""" Generate a random domain assignment to start the Metropolis walk"""

		swCount = self.topology.getSwitchCount()
		domainSize = swCount / self.numDomains # We divide the routers equally across the domains

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
						if currDomain >= self.numDomains : continue
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
						# 		self.switchDomains[sw] = random.randint(0, self.numDomains - 1)
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
			if self.switchDomains[sw] not in self.domains : 
				self.domains[self.switchDomains[sw]] = [sw]
			else : 
				if sw not in self.domains[self.switchDomains[sw]] : 
					self.domains[self.switchDomains[sw]].append(sw)

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

		# Check if domains are contiguous. We do this by starting at a switch, and
		# check if all switches in the domain are reachable inside the domain. 
		for domain in self.domains.keys() : 
			domainSwitches = self.domains[domain]
			reachableSwitches = [domainSwitches[0]]
			switchQueue = [domainSwitches[0]]

			while len(reachableSwitches) < len(domainSwitches):
				if len(switchQueue) == 0 : 
					# Partition in domain. Not valid! 
					return False
				sw = switchQueue.pop(0)
				neighbours = self.topology.getSwitchNeighbours(sw)
				for n in neighbours :
					if self.switchDomains[n] == domain : 
						if n not in reachableSwitches : 
							reachableSwitches.append(n)
							switchQueue.append(n)


		return True	


	def computeDomainAssignmentScore(self) :
		""" Computes the score of a particular domain assignment """
		
















		





