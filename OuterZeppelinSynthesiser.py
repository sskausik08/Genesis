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
from ZeppelinSynthesiser import ZeppelinSynthesiser

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
		self.MCMC_MAX_ITER = 50000	
		self.beta = 0.3 # Constant

		# Scoring State variables 
		self.ASPaths = dict()
		self.ASPositions = dict()

		# Profiling variables
		self.worstConfScore = 0
		self.bestConfScore = 1000000000000000000
		self.worstRFScore = 0
		self.bestRFScore = 1000000000000000000

		self.confScoreTime = 0
		self.rfScoreTime = 0
		self.continuityTime = 0


	def enforceDAGs(self, dags, paths, endpoints, numDomains=5):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.paths = copy.deepcopy(paths)
		self.endpoints = copy.deepcopy(endpoints)
		self.numDomains = numDomains

		swCount = self.topology.getSwitchCount()

		start_t = time.time() 	

		self.MCMCWalk()

		RFCount = 0
		# Found a domain assignment from MCMC. Solve the OSPF domains now.
		for domain in range(self.numDomains) :
			topo = self.getDomainTopology(domain)

			pdb = PolicyDatabase()
			print "domain", domain
			[dags, endpoints] = self.getDomainDAGs(domain, pdb, topo)

			for dst in dags : 
				pdb.addDestinationDAG(dst, dags[dst])

			zepSynthesiser = ZeppelinSynthesiser(topo, pdb)
			routeFilters = zepSynthesiser.enforceDAGs(dags, endpoints)

			for dst in routeFilters : 
				RFCount += len(routeFilters[dst])

		print "RF Count is", RFCount
		print self.domains
		print "Best configuration score", self.bestConfScore, "Worst configuration score", self.worstConfScore
		print "Best RF score", self.bestRFScore, "Worst RF score", self.worstRFScore
		end_t = time.time()
		print "Time taken  for MCMC is ", end_t - start_t
		print "Conf Score Time", self.confScoreTime
		print "Continuity Time", self.rfScoreTime

	def MCMCWalk(self) :
		# Start a MCMC sampling walk with number of domains=self.numDomains. 
		
		self.MCMCIter = 0	
		
		# MCMC Algorithm initial step: start with a preliminary domain assignment (chosen at random)
		self.computeRandomDomainAssignment()
		self.computeBoundaries() # boundary bookkeeping for efficiency 

		# Find diamonds for route-filter calculations. 
		self.findDiamonds()

		worstScore = 0
		bestScore = 1000000000000000000

		# Perform the Metropolis walk using the score functions. 
		# We consider solutions with a smaller score to be better. 
		Score = self.computeDomainAssignmentScore()

		for self.MCMCIter in range(self.MCMC_MAX_ITER):
			if Score > worstScore : worstScore = Score
			if Score < bestScore : bestScore = Score

			change = self.giveRandomDomainChange()

			# Make the random change to domain assignment.
			sw = change[0]
			oldDomain = self.switchDomains[sw]
			newDomain = change[1]
			self.switchDomains[sw] = newDomain 

			# recompute boundaries
			self.recomputeBoundaries(sw, oldDomain, newDomain)

			# Check if domain is continuous
			s_t = time.time()
			if not self.checkDomainContinuity(oldDomain) :
				# Do not accept change. 
				self.switchDomains[sw] = oldDomain
				self.recomputeBoundaries(sw, newDomain, oldDomain)
				continue

			self.continuityTime += time.time() - s_t

			# Compute new score. 
			newScore = self.computeDomainAssignmentScore()

			transitionProbability = math.exp(- self.beta * (float(newScore) - float(Score)))

			# if transitionProbability >= 1:
			# 	# Surely transition to new state
			# 	print "Score", Score, newScore, " Accept"
			# 	continue
			# else:
			transition = self.flip(transitionProbability) 
			if transition :	
				# accept transition to new state
				Score = newScore # Update the score as we accept transition
				#print "Score", Score, newScore, " Accept", sw, oldDomain, newDomain, worstScore, bestScore
				continue
			else :
				# Do not transition. Revert back change.
				#print "Score", Score, newScore, " Reject", sw, oldDomain, newDomain, worstScore, bestScore
				self.switchDomains[sw] = oldDomain
				self.recomputeBoundaries(sw, newDomain, oldDomain)

		print "Best score", bestScore, "Worst score", worstScore
		print "Best configuration score", self.bestConfScore, "Worst configuration score", self.worstConfScore
		print "Best RF score", self.bestRFScore, "Worst RF score", self.worstRFScore
		

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
		reachableSwitches = dict()
		reachableSwitches[domainSwitches[0]] = True
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
						reachableSwitches[n] = True
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

	def computeDomainAssignmentScore(self, sw=None, oldDomain=None, newDomain=None) :
		""" Computes the score of a particular domain assignment """
		
		score = 1

		score += 0.1*self.domainSizeScore()
		score += self.BGPCompabitityScore()
		score += 2*self.numberBGPRoutersScore()
		score += 2*self.domainSizeDeviationScore()

		start_t = time.time()
		if self.MCMCIter % 100 == 0 : 
			confScore = self.configurationScore()
			self.prevConfScore = confScore
		else : 
			confScore = self.prevConfScore + self.findConfScoreDiff(sw, oldDomain, newDomain)
		self.confScoreTime += time.time() - start_t
		if confScore > self.worstConfScore : 
			self.worstConfScore = confScore
		if confScore < self.bestConfScore : 
			self.bestConfScore = confScore
		
		score += 2*confScore

		rfScore = self.routeFilterScore()
		if rfScore > self.worstRFScore : 
			self.worstRFScore = rfScore
		if rfScore < self.bestRFScore : 
			self.bestRFScore = rfScore

		score += 2*rfScore

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
		score = 0

		for pc in self.paths.keys() :
			path = self.paths[pc] 
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

			# Store computations in state
			self.ASPaths[pc] = aspath
			self.ASPositions[pc] = aspositions

			score += self.findConfScore(path, aspath, aspositions)

		return score

	def findConfScore(self, path, aspath, aspositions) :
		""" Find conf score for a single path """
		src = path[0]
		dst = path[len(path) - 1]

		score = 0

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

			# Local preference scores	
			for i in range(lastNonLoopDownstreamPath+1, len(aspath) - 1) :
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
					# score += 1 
					score += 0
				else : 
					# Check if d1-d2 is on the unique shortest AS path to destination AS
					[uniqueness, aspath1] = self.findShortestASPath(domain1, aspath[len(aspath) - 1])
					if not uniqueness : 
						# Shortest AS path not unique. Require 1 local preference entry
						# score += 1
						score += 0
					else: 
						# Shortest AS path is unique, see if it contains d1->d2
						if aspath1[1] == domain2 : 
							# Unique shortest AS path goes from d1 to d2. 
							score += 0
						else : 
							# d1 -> d2 not on shortest AS path. Require 1 local preference entry
							# score += 1
							score += 0

		return score

	def findConfScoreDiff(self, sw, oldDomain, newDomain) :
		""" Find difference in scores as sw oldDomain -> newDomain """
		scoreDiff = 0

		for pc in self.paths.keys() : 
			path = self.paths[pc]
			src = path[0]
			dst = path[len(path) - 1]

			if sw not in path : 
				# Not change in score? 
				continue

			# sw is in path, so domain has changed. Check if affected. 
			oldaspath = self.ASPaths[pc]
			oldaspositions = self.ASPositions[pc]
			oldScore = self.findConfScore(path, oldaspath, oldaspositions)

			newaspath = [self.switchDomains[src]]
			newaspositions = [0] # Store the positions when the AS first starts.
			for i in range(1, len(path)) : 
				domain = self.switchDomains[path[i]]
				if domain != newaspath[len(newaspath) - 1] : 
					# Next AS. Add to AS path
					newaspath.append(domain)
					newaspositions.append(i)

			newscore = self.findConfScore(path, newaspath, newaspositions)

			scoreDiff = scoreDiff - oldScore + newScore


		return scoreDiff
			

	def findShortestASPath(self, srcDomain, dstDomain) :
		""" Find shortest path from src to dst domains. Return uniqueness of shortest path as well"""
		s_t = time.time()
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
						self.rfScoreTime += time.time() - s_t 
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
						self.rfScoreTime += time.time() - s_t 
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


	def findDiamonds(self) :
		""" Detecting diamonds in the different dags. A diamond is 
		defined as a subgraph of the overlay where there are two paths from s to t
		such that the two paths belong to different destination Dags. This implies that
		there are two shortest paths from s to t which is not enforceable with route filtering """
		swCount = self.topology.getSwitchCount()
		dsts = self.pdb.getDestinationSubnets()
		
		self.diamondPaths = [[0 for x in range(swCount + 1)] for x in range(swCount + 1)]
		
		for dst1 in dsts :
			for dst2 in dsts : 
				if dst1 >= dst2 : continue 
				dag1 = self.destinationDAGs[dst1]
				dag2 = self.destinationDAGs[dst2]

				for swDiv in dag1 : 
					if dag1[swDiv] == None : continue 
					# Detect a diamond
					if swDiv in dag2 : 
						if dag2[swDiv] == None : continue
						# swDiv in the dag. Check if both dags diverge
						if dag1[swDiv] != dag2[swDiv] : 
							# Diverging common switches, search for intersecting switch
							dstpath1 = [dag1[swDiv]] 
							nextsw = dag1[dag1[swDiv]]
							while nextsw != None:
								dstpath1.append(nextsw)
								nextsw = dag1[nextsw]
							dstpath2 = [dag2[swDiv]]
							nextsw = dag2[dag2[swDiv]]
							while nextsw != None:
								dstpath2.append(nextsw)
								nextsw = dag2[nextsw]
							# dstpath1 and dstpath2 are paths from sw to their respective destinations
							# Find intersection

							for swConv in dstpath1 : 
								if swConv in dstpath2 : 
									# Intersection! This is the smallest diamond starting at swDiv
									self.diamondPaths[swDiv][swConv] += 1
									break


	def routeFilterScore(self) :
		# Score based on number of OSPF filters required in each domain.
		# This is overapproximated by number of diamonds in each domain.

		score = 0
		for domain in range(self.numDomains) :
			for sw1 in self.domains[domain] : 
				for sw2 in self.domains[domain] :
					if self.diamondPaths[sw1][sw2] != 0 : 
						# There are diamonds in the domain. 
						# Will require atmost 1 route filter for each diamond.
						score += self.diamondPaths[sw1][sw2]

		return score

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


	def getDomainTopology(self, domain) :
		""" Constructs the topology object for domain"""
		topo = Topology(name="domain"+str(domain))

		for sw in self.domains[domain] :
			domainNeighbours = []
			for n in self.topology.getSwitchNeighbours(sw) :
				if self.switchDomains[n] == domain : 
					domainNeighbours.append(self.topology.getSwName(n))
			topo.addSwitch(self.topology.getSwName(sw), domainNeighbours)
			
		return topo

	def getDomainDAGs(self, domain, pdb, topology) : 
		""" Returns DAGs and endpoints for domain. Side-effect: Sets up pdb with the paths """
	
		# endpoints.append([sw, dst])
		# pc = self.pdb.addReachabilityPolicy(dst, sw, dstSw)
		# pdb.addPath(pc, path)
		dags = dict()
		endpoints = []

		for pc in self.paths.keys() : 
			path = self.paths[pc]
			src = path[0]
			dst = path[len(path) - 1]

			aspath = [self.switchDomains[src]]
			aspositions = [0] # Store the positions when the AS first starts.
			for i in range(1, len(path)) : 
				d = self.switchDomains[path[i]]
				if d != aspath[len(aspath) - 1] : 
					# Next AS. Add to AS path
					aspath.append(d)
					aspositions.append(i)

			if len(aspath) == 1 : 
				# The entire path is the same domain
				if aspath[0] == domain : 
					# Add this to pdb. 
					domainpath = path
					
					topopath = []
					for sw in domainpath :
						if self.switchDomains[sw] != domain :
							print sw, self.topology.getSwName(sw), self.switchDomains[sw], domain
						topopath.append(topology.getSwID(self.topology.getSwName(sw)))

					subnet = self.pdb.getDestinationSubnet(pc)
					dpc = pdb.addReachabilityPolicy(subnet, topopath[0], topopath[len(topopath) - 1])
					pdb.addPath(dpc, topopath)
					endpoints.append([topopath[0], subnet])

					# Add path to Dag of subnet
					if subnet not in dags :
						dags[subnet] = dict()
					
					dags[subnet][topopath[len(topopath) - 1]] = None
					for i in range(len(topopath) - 1) :
						dags[subnet][topopath[i]] = topopath[i + 1]

			else : 
				# Find longest path from destination which does not contain loops
				i = len(aspath) - 1
				lastNonLoopDownstreamPath = -1
				while i > 0:
					d = aspath[i]
					if aspath.count(d) > 1 : 
						# Domain part of loop.
						for j in range(i - 1, -1, -1) :
							if aspath[j] == d :
								# First repitition from the end. 
								if j > lastNonLoopDownstreamPath :
									lastNonLoopDownstreamPath = j
					i -= 1

				# A looped path. Add static routing till start of (lastNonLoopDownstreamPath + 1)th AS
				# Routing from (lastNonLoopDownstreamPath + 1)th AS to destination is loop-free
				index = -1
				for j in range(lastNonLoopDownstreamPath + 1, len(aspath)) : 
					if aspath[j] == domain : 
						index = j
					break

				if index > -1 : 
					if index == len(aspath) - 1: 
						domainpath = path[aspositions[index]:] # Extracts the path in the last domain.
					else :
						domainpath = path[aspositions[index]:aspositions[index + 1]] # Extracts the path in the domain.

					topopath = []
					for sw in domainpath :
						if self.switchDomains[sw] != domain :
							print sw, self.topology.getSwName(sw), self.switchDomains[sw], domain
							exit(0)
						topopath.append(topology.getSwID(self.topology.getSwName(sw)))

					subnet = self.pdb.getDestinationSubnet(pc)
					dpc = pdb.addReachabilityPolicy(subnet, topopath[0], topopath[len(topopath) - 1])
					pdb.addPath(dpc, topopath)
					endpoints.append([topopath[0], subnet])

					# print aspath, lastNonLoopDownstreamPath, path, self.pdb.getDestinationSubnet(pc), domainpath
					# Add path to Dag of subnet
					if subnet not in dags :
						dags[subnet] = dict()
					
					dags[subnet][topopath[len(topopath) - 1]] = None
					for i in range(len(topopath) - 1) :
						dags[subnet][topopath[i]] = topopath[i + 1]
		# print dags
		return [dags, endpoints]
		





