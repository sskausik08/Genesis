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

		# Domain size variables
		self.domainUpperLimit = 50
		self.domainLowerLimit = 10

		# BGP compatibility
		self.nonBGPCompatibleSwitches = []
		# MCMC variables 
		self.MCMC_MAX_ITER = 5000
		self.beta = 1.00 # Constant

		# Profiling variables
		self.worstConfScore = 0
		self.bestConfScore = 1000000000000000000


	def enforceDAGs(self, dags, paths, endpoints, numDomains=5):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.paths = copy.deepcopy(paths)
		self.endpoints = copy.deepcopy(endpoints)
		self.numDomains = numDomains

		swCount = self.topology.getSwitchCount()

		start_t = time.time() 	

		self.MCMCWalk()

	

	def MCMCWalk(self) :
		# Start a MCMC sampling walk with number of domains=self.numDomains. 
		
		iteration = 0
		
		# MCMC Algorithm initial step: start with a preliminary domain assignment (chosen at random)
		self.computeRandomDomainAssignment()
		self.computeBoundaries() # boundary bookkeeping for efficiency

		worstScore = 0
		bestScore = 1000000000000000000

		# Perform the Metropolis walk using the score functions. 
		# We consider solutions with a smaller score to be better. 
		for iteration in range(self.MCMC_MAX_ITER):
			oldScore = self.computeDomainAssignmentScore()
			if oldScore > worstScore : worstScore = oldScore
			if oldScore < bestScore : bestScore = oldScore

			change = self.giveRandomDomainChange()

			# Make the random change to domain assignment.
			sw = change[0]
			oldDomain = self.switchDomains[sw]
			newDomain = change[1]
			self.switchDomains[sw] = newDomain 

			# recompute boundaries
			self.recomputeBoundaries(sw, oldDomain, newDomain)

			# Check if domain is continuous
			if not self.checkDomainContinuity(oldDomain) :
				# Do not accept change. 
				self.switchDomains[sw] = oldDomain
				self.recomputeBoundaries(sw, newDomain, oldDomain)
				continue

			# Compute new score. 
			newScore = self.computeDomainAssignmentScore()

			transitionProbability = math.exp(- self.beta * (float(newScore) - float(oldScore)))

			# if transitionProbability >= 1:
			# 	# Surely transition to new state
			# 	print "Score", oldScore, newScore, " Accept"
			# 	continue
			# else:
			transition = self.flip(transitionProbability) 
			if transition :	
				# accept transition to new state
				print "Score", oldScore, newScore, " Accept", sw, oldDomain, newDomain, worstScore, bestScore
				continue
			else :
				# Do not transition. Revert back change.
				print "Score", oldScore, newScore, " Reject", sw, oldDomain, newDomain, worstScore, bestScore
				self.switchDomains[sw] = oldDomain
				self.recomputeBoundaries(sw, newDomain, oldDomain)

		print "Best score", bestScore, "Worst score", worstScore
		print "Best configuration score", self.bestConfScore, "Worst configuration score", self.worstConfScore
		print self.domains

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
			
			if len(self.domains[domain]) == 1 : 
				# Domain size is 1, dont change it (to preserve number of domains)
				continue

			if sw not in self.boundarySwitches[domain] : 
				# sw not a boundary switch, can't change its domain.
				continue
			else : 
				# sw is a boundary switch. Check if sw partitions the domain.
				neighbours = self.topology.getSwitchNeighbours(sw)
				neighbouringDomains = []
				for n in neighbours : 
					ndomain = self.switchDomains[n]
					if ndomain != domain and ndomain not in neighbouringDomains : 
						neighbouringDomains.append(ndomain)

				if len(neighbouringDomains) == 0 : 
					# ERROR! 
					print sw, domain, neighbours

				# pick one neighbouring domain by random and change sw's domain
				newDomain = neighbouringDomains[random.randint(0, len(neighbouringDomains) - 1)]
				# Return the random domain change picked. 
				return [sw, newDomain] 


	def computeBoundaries(self) : 
		""" Computes the boundaries of the domains"""
		self.boundarySwitches = dict()
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

		for sw in range(1, swCount + 1) :
			if self.switchDomains[sw] not in self.domains : 
				self.domains[self.switchDomains[sw]] = [sw]
			else : 
				if sw not in self.domains[self.switchDomains[sw]] : 
					self.domains[self.switchDomains[sw]].append(sw)


	def recomputeBoundaries(self, sw, oldDomain, newDomain):
		""" Recompute boundaries for change"""

		# Move sw from oldDomain to newDomain
		self.domains[oldDomain].remove(sw)
		self.domains[newDomain].append(sw)
		
		# Shift boundaries
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
		

	def checkDomainContinuity(self, domain) : 
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
		
		score = 1

		score += 0.1*self.domainSizeScore()
		score += self.BGPCompabitityScore()
		score += 1*self.numberBGPRoutersScore()
		score += 10*self.domainSizeDeviationScore()

		confScore = self.configurationScore()
		if confScore > self.worstConfScore : 
			self.worstConfScore = confScore
		if confScore < self.bestConfScore : 
			self.bestConfScore = confScore
		
		score += 2*confScore
		return score
		

	def domainSizeScore(self) : 
		# compute domain size (if in range or not).
		score = 0
		swCount = self.topology.getSwitchCount() 
		
		for domain in range(self.numDomains) :
			domainSize = len(self.domains[domain])

			# if domainSize > self.domainLowerLimit and domainSize < self.domainUpperLimit : 
				# Within range, score not changed.
			score += pow(abs((self.domainLowerLimit + self.domainUpperLimit)/2 - domainSize), 2)
			# else : 
			# 	score += 100

		return score

	def BGPCompabitityScore(self) :
		score = 0

		for sw in self.nonBGPCompatibleSwitches : 
			domain = self.switchDomains[sw]
			if sw in self.boundarySwitches[domain] :
				# non BGP-compatible router requires BGP
				score += 100

		return score

	def numberBGPRoutersScore(self) : 
		score = 0

		for domain in range(self.numDomains) : 
			score += len(self.boundarySwitches[domain])

		return score

	def configurationScore(self) : 
		""" Computes the extra lines of BGP required to enforce policy routing 
		in the inter-domain setting """
		self.destinationRoute = dict()

		score = 0

		for path in self.paths.values() : 
			src = path[0]
			dst = path[len(path) - 1]

			aspath = [self.switchDomains[src]]
			aspositions = [0] # Store the positions when the AS first starts.
			for i in range(1, len(path)) : 
				domain = self.switchDomains[path[i]]
				if domain != aspath[len(aspath) - 1] : 
					# Next AS. Add to AS path
					aspath.append(domain)
					aspositions.append(i)

			if len(aspath) == 1 : 
				# The entire path is the same domain, there is no BGP configuration required for this path
				score += 0

			else : 
				# Find longest path from destination which does not contain loops
				i = len(aspath) - 1
				lastNonLoopDownstreamPath = -1
				while i > 0:
					domain = aspath[i]
					if aspath.count(domain) > 1 : 
						# Domain part of loop.
						for j in range(i - 1, -1, -1) :
							if aspath[j] == domain :
								# First repitition from the end. 
								if j > lastNonLoopDownstreamPath :
									lastNonLoopDownstreamPath = j
					i -= 1


				if lastNonLoopDownstreamPath > -1 : 
					# A looped path. Add static routing till start of (lastNonLoopDownstreamPath + 1)th AS
					# Routing from (lastNonLoopDownstreamPath + 1)th AS to destination is loop-free
					posSw = aspositions[lastNonLoopDownstreamPath + 1] 
					
					# Static routing cost is the number of rules required till posSw
					score += posSw

					# Truncate as path to loop-free to find local pref scores
					aspath = aspath[lastNonLoopDownstreamPath + 1:] 

				# Local preference scores	
				for i in range(len(aspath) - 1) :
					domain1 = aspath[i]
					domain2 = aspath[i + 1]		
					
					boundary1 = self.boundarySwitches[domain1]
					boundary2 = self.boundarySwitches[domain2]

					linkCount = 0 # Denotes the number of links connecting domains 1 & 2
					for sw in boundary1 : 
						neighbours = self.topology.getSwitchNeighbours(sw)
						for n in neighbours : 
							if n in boundary2 : 
								linkCount += 1 # AS1-AS2 link

				if linkCount > 1 : 
					# Multiple links connecting the AS. Require 1 local preference entry
					score += 1
				else : 
					# Check if d1-d2 is on the unique shortest AS path to destination AS
					[uniqueness, aspath1] = self.findShortestASPath(domain1, aspath[len(aspath) - 1])
					if not uniqueness : 
						# Shortest AS path not unique. Require 1 local preference entry
						score += 1
					else: 
						# Shortest AS path is unique, see if it contains d1->d2
						if aspath1[1] == domain2 : 
							# Unique shortest AS path goes from d1 to d2. 
							score += 0
						else : 
							# d1 -> d2 not on shortest AS path. Require 1 local preference entry
							score += 1

		return score


	def findShortestASPath(self, srcDomain, dstDomain) :
		""" Find shortest path from src to dst domains. Return uniqueness of shortest path as well"""
		srcBoundary = self.boundarySwitches[srcDomain]
		dstBoundary = self.boundarySwitches[dstDomain]

		# Do a Breadth-first search from srcDomain to dstDomain
		domainQueue1 = [srcDomain]
		domainQueue2 = []
		visited = dict()
		bfstree = dict()
		paths = dict()
		paths[srcDomain] = 1

		while len(domainQueue1) > 0 :
			# Explore one level of tree
			while len(domainQueue1) > 0:
				d = domainQueue1.pop(0)
				visited[d] = True 

				if d == dstDomain : 
					if paths[d] > 1 :
						# Multiple shortest paths to dstDomain. 
						return [False, None]
					else : 
						# Single Unique shortest path to dstDomain. 
						# Trace back path to src and return.
						aspath = [dstDomain]
						nextas = bfstree[dstDomain]
						while nextas != srcDomain :
							aspath.append(nextas)
							nextas = bfstree[nextas]
						aspath.append(srcDomain)
						# Reverse aspath.
						aspath.reverse()
						return [True, aspath]

				# Find neighbouring domains
				neighbouringDomains = []
				boundary = self.boundarySwitches[d]
				for sw in boundary :
					for n in self.topology.getSwitchNeighbours(sw) :
						nd = self.switchDomains[n]
						if nd != d and nd not in neighbouringDomains:
							neighbouringDomains.append(nd)
					
				for nd in neighbouringDomains :
					if nd not in visited :
						if nd not in domainQueue2 : 
							domainQueue2.append(nd)
							paths[nd] = paths[d]
							bfstree[nd] = d
						else : 
							paths[nd] += paths[d]

			domainQueue1 = domainQueue2
			domainQueue2 = []



		


	def domainSizeDeviationScore(self) : 
		# Score to ensure deviation of domain sizes is small. 

		mean = 0
		for domain in range(self.numDomains) : 
			mean += len(self.domains[domain])
		mean = float(mean) / float(self.numDomains)

		variance = 0
		for domain in range(self.numDomains) : 
			variance += pow(len(self.domains[domain]) - mean, 2)
		variance = float(variance) / float(self.numDomains)
		deviation = math.sqrt(variance)

		return deviation











		





