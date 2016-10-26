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
	def __init__(self, topology, pdb, numDomains=5, timeout=300) :
		self.topology = topology
		self.pdb = pdb
	

		# Store switch domains for each switch
		self.switchDomains = dict()
		self.domains = dict()
		self.boundarySwitches = dict()

		# Domain size variables
		self.domainUpperLimit = 40
		self.domainLowerLimit = 10

		# Domain Assignments
		self.bestDomainAssignment = None
		self.worstDomainAssigmentRF = None

		# BGP compatibility
		self.nonBGPCompatibleSwitches = []
		

		# MCMC variables 
		self.numDomains = numDomains
		self.MCMC_MAX_ITER = 10000000	
		self.MCMC_MAX_TIME = timeout # in seconds
		self.beta = 0.045 # Constant

		# Scoring State variables 
		self.ASPaths = dict()
		self.ASPositions = dict()
		self.lastNonLoopDownstreamPosition = dict()
		self.bgpRouterCounts = defaultdict(lambda:defaultdict(lambda:None))
		self.shortestASPaths = defaultdict(lambda:defaultdict(lambda:None))

		# Cache neighbours for reduced times.
		self.topologyNeighbours = None

		# Profiling variables
		self.worstConfScore = 0
		self.bestConfScore = 1000000000000000000
		self.worstRFScore = 0
		self.bestRFScore = 1000000000000000000

		self.confScoreTime = 0
		self.rfScoreTime = 0
		self.continuityTime = 0
		self.domainChangeTime = 0


	def enforceDAGs(self, dags, paths, endpoints):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.paths = copy.deepcopy(paths)
		self.endpoints = copy.deepcopy(endpoints)
		self.topologyNeighbours = self.topology.getNeighbours()
		self.swCount = self.topology.getSwitchCount()

		if not self.topology.checkTopologyContinuity() :
			print "Topology not connected"
			exit(0)

		start_t = time.time() 		
		self.MCMCWalk()
		mcmcTime = time.time() - start_t

		print "Best Configuration"
		self.switchDomains = self.bestDomainAssignment 
		self.computeBoundaries()
		print self.domains
		start_t = time.time() 
		bestRFCount = self.synthesizeOSPFConfigurations()
		self.bestConfScore = self.configurationScore()
		ospfTime = time.time() - start_t

		print "Worst RF Configuration"
		worstRFCount = self.synthesizeOSPFConfigurations(self.worstDomainAssigmentRF)

		print "Config Improvement", float(self.bestConfScore)/float(self.worstConfScore), self.bestConfScore, self.worstConfScore
		print "RF Improvement", float(bestRFCount)/float(worstRFCount), bestRFCount, worstRFCount
		print "RF scores", self.worstRFScore, self.bestRFScore
		end_t = time.time()
		print "Time taken  for MCMC is (and iterations), and OSPF time", end_t - start_t, self.MCMCIter
		print "Conf Score Time", self.confScoreTime
		print "RF Score Time", self.rfScoreTime
		print "Continuity Time", self.continuityTime
		print "Domain Change Time", self.domainChangeTime


		self.zepFile = open("zeppelin-timing", 'a')
		self.zepFile.write("Time taken  for MCMC is (and iterations), and OSPF time " + str(mcmcTime) + " " + str(self.MCMCIter) + " " + str(ospfTime))
		self.zepFile.write("\n")
		self.zepFile.write("Config Improvement " + str(float(self.bestConfScore)/float(self.worstConfScore)) + " " + str(self.bestConfScore) + " " + str(self.worstConfScore))
		self.zepFile.write("\n")
		self.zepFile.write("RF Improvement " + str(float(bestRFCount)/float(worstRFCount)) + " " + str(bestRFCount) + " " + str(worstRFCount))
		self.zepFile.write("\n")

	def MCMCWalk(self) :
		# Start a MCMC sampling walk with number of domains=self.numDomains. 
		print "Starting MCMC Walk"
		self.MCMCIter = 0	

		# Find diamonds for route-filter calculations. 
		self.findDiamonds()


		# MCMC Algorithm initial step: start with a preliminary domain assignment (chosen at random)
		self.computeRandomDomainAssignment()
		self.computeBoundaries() # boundary bookkeeping for efficiency 

		worstScore = 0
		bestScore = 1000000000000000000

		# Perform the Metropolis walk using the score functions. 
		# We consider solutions with a smaller score to be better. 
		Score = self.computeDomainAssignmentScore()

		print "Started MCMC walk"
		MCMCStartTime = time.time()
		for self.MCMCIter in range(self.MCMC_MAX_ITER):
			
			# Check if timed out every 10000 iteration
			if self.MCMCIter % 10000 == 0 :
				if time.time() - MCMCStartTime > self.MCMC_MAX_TIME : 
					# MCMC timed out. 
					break

			if Score > worstScore : worstScore = Score
			if Score < bestScore : 
				bestScore = Score
				self.bestDomainAssignment = copy.deepcopy(self.switchDomains)

			s_t = time.time()
			change = self.giveRandomDomainChange()
			self.domainChangeTime += time.time() - s_t

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

			transition = self.flip(transitionProbability) 
			if transition :	
				# accept transition to new state
				Score = newScore # Update the score as we accept transition
				#print "Score", Score, newScore, " Accept", sw, oldDomain, newDomain, worstScore, bestScore, transitionProbability
				continue
			else :
				# Do not transition. Revert back change.
				#print "Score", Score, newScore, " Reject", sw, oldDomain, newDomain, worstScore, bestScore, transitionProbability
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
		
		iteration = 0
		iterationCount = 5000 # Not assigned based on anything! 

		for iteration in range(iterationCount) : 
			sw = random.randint(1, self.swCount) 
			domain = self.switchDomains[sw]
			
			if len(self.domains[domain]) <= self.domainLowerLimit: 
				# Domain size will be violated if we change a switch of this domain. 
				# Dont change it (to preserve number of domains)
				continue

			if sw not in self.boundarySwitches[domain] : 
				# sw not a boundary switch, can't change its domain.
				continue
			else : 
				# sw is a boundary switch. Check if sw partitions the domain.
				neighbours = self.topologyNeighbours[sw]
				neighbouringDomains = []
				for n in neighbours : 
					ndomain = self.switchDomains[n]
					if ndomain != domain and ndomain not in neighbouringDomains : 
						neighbouringDomains.append(ndomain)

				if len(neighbouringDomains) == 0 : 
					# ERROR! 
					print sw, domain, neighbours
					exit(0)

				# pick one neighbouring domain by random and change sw's domain
				newDomain = neighbouringDomains[random.randint(0, len(neighbouringDomains) - 1)]

				if len(self.domains[newDomain]) + 1 >= self.domainUpperLimit :
					# New domain's size would exceed upper limit. Reject change.
					continue

				# Return the random domain change picked. 
				return [sw, newDomain] 

		# Could not find a random change.
		print "ERROR: No change in domain found"
		exit(0)

	def computeBoundaries(self) : 
		""" Computes the boundaries of the domains"""
		self.boundarySwitches = dict()
		for sw in range(1, self.swCount + 1) :
			neighbours = self.topologyNeighbours[sw]
			for n in neighbours : 
				if self.switchDomains[sw] != self.switchDomains[n] :
					# Boundary
					if self.switchDomains[sw] not in self.boundarySwitches :
						self.boundarySwitches[self.switchDomains[sw]] = [sw]
					else : 
						self.boundarySwitches[self.switchDomains[sw]].append(sw)
					break

		for sw in range(1, self.swCount + 1) :
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

		neighbours = self.topologyNeighbours[sw]

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
			neighbours = self.topologyNeighbours[sw]
			for n in neighbours :
				if self.switchDomains[n] == domain : 
					if n not in reachableSwitches and n not in switchQueue : 
						reachableSwitches[n] = True
						switchQueue.append(n)	

		return True

	def isBoundarySwitch(self, sw): 
		""" Returns if sw is a boundary switch or not"""
		neighbours = self.topologyNeighbours[sw]
		for n in neighbours : 
			if self.switchDomains[sw] != self.switchDomains[n] :
				return True

		return False

	def computeRandomDomainAssignment(self):
		""" Generate a random domain assignment to start the Metropolis walk"""

		switches = range(1, self.swCount + 1)
		iterations = 50000
		
		self.switchDomains = dict()
		for itr in range(iterations) :
			# print "Iteration", itr
			currDomain = 0
			self.switchDomains = dict()
			domainSizes = dict()
			for domain in range(self.numDomains) : 
				domainSizes[domain] = 0

			while len(self.switchDomains) != self.swCount:
				random.shuffle(switches)
				assignedSwitchCount = len(self.switchDomains)
				for sw in switches :
					if sw in self.switchDomains:
						# Switch assigned. 
						continue

					neighbours = self.topologyNeighbours[sw]
					neighbouringDomains = dict()
					assignedNeighbour = False
					for n in neighbours : 
						if n in self.switchDomains:
							# Neighbour assigned
							neighbouringDomains[self.switchDomains[n]] = True
							assignedNeighbour = True

					if currDomain >= self.numDomains : 						
						if len(neighbouringDomains.keys()) == 0 :
							# No neighbour assigned
							continue
						else : 
							# Pick domain with minimum size 
							sortedDomains = []

							for d in neighbouringDomains.keys() :
								sortedDomains.append([d, neighbouringDomains[d]])

							sortedDomains = sorted(sortedDomains, key=lambda p: p[1])

							for d in sortedDomains :
								domain = d[0]
								currentSize = domainSizes[domain]
								newSize = min(self.domainUpperLimit, currentSize + 2) # Weird constant
								switchQueue = [sw]

								while len(switchQueue) > 0 and domainSizes[domain] < newSize :
									sw1 = switchQueue.pop(0)
									neighbours = self.topologyNeighbours[sw1]
									if sw1 not in self.switchDomains : 
										# switch not assigned
										self.switchDomains[sw1] = domain
										# print sw1, domain
										domainSizes[domain] += 1

									for n in neighbours : 
										if n not in self.switchDomains and n not in switchQueue:
											switchQueue.append(n) 
						
					else : 
						# Check if any neighbours are assigned to some domain. Then dont assign.
						if len(neighbouringDomains.keys()) > 0 :
							continue 

						self.switchDomains[sw] = currDomain
						domainSizes[currDomain] += 1
						# Do a BFS from this switch till we exceed lower limit
						switchQueue = [sw]
						while len(switchQueue) > 0 and domainSizes[currDomain] < self.domainLowerLimit :
							sw1 = switchQueue.pop(0)
							neighbours = self.topologyNeighbours[sw1]
							if sw1 not in self.switchDomains : 
								# switch not assigned
								self.switchDomains[sw1] = currDomain
								# print sw1, currDomain
								domainSizes[currDomain] += 1
							for n in neighbours : 
								if n not in self.switchDomains and n not in switchQueue:
									switchQueue.append(n) 

						if domainSizes[currDomain] < self.domainLowerLimit :
							# BFS could not find a domain with size greater than lower limit, Find a new assignment
							break
							
						# print "Size", currDomain, domainSizes[currDomain]
						currDomain += 1

				if len(self.switchDomains) == assignedSwitchCount and len(self.switchDomains) != self.swCount:
					# No switch assigned in this pass. Find a new assignment
					break


			# Check validity
			if not self.checkValidDomainAssignment() : 
				continue
			else :
				break
		if itr >= iterations - 1 : 
			print "Cannot find a random domain assignment satisfying input policies even after 20k iterations"
			exit(0)


	def checkValidDomainAssignment(self) :	
		# Checks the validity of a particular domain assignment.
		if len(self.switchDomains) != self.swCount :
			# print "Size"
			return False

		self.domains = dict()
		for sw in range(1, self.swCount + 1) :
			if self.switchDomains[sw] not in self.domains : 
				self.domains[self.switchDomains[sw]] = [sw]
			else : 
				if sw not in self.domains[self.switchDomains[sw]] : 
					self.domains[self.switchDomains[sw]].append(sw)


			# A switch must be connected to atleast one switch of the same domain. (Assuming no single switch domains)
			neighbours = self.topologyNeighbours[sw]
			isConnected = False
			for n in neighbours : 
				if self.switchDomains[sw] == self.switchDomains[n] :
					isConnected = True
			if not isConnected :
				# No neighbour in same domain. Not a valid assignment
				# print "No neighbours"
				return False

		for domain in range(self.numDomains) :
			if len(self.domains[domain]) < self.domainLowerLimit or len(self.domains[domain]) > self.domainUpperLimit:
				# Domain size violated.
				# print "Domain size violated"
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
					# print "Partition" 
					return False
				sw = switchQueue.pop(0)
				neighbours = self.topologyNeighbours[sw]
				for n in neighbours :
					if self.switchDomains[n] == domain : 
						if n not in reachableSwitches : 
							reachableSwitches.append(n)
							switchQueue.append(n)


		return True	

	def computeDomainAssignmentScore(self, sw=None, oldDomain=None, newDomain=None) :
		""" Computes the score of a particular domain assignment """
		
		score = 1

		#score += 0.1*self.domainSizeScore()
		score += self.BGPCompabitityScore()
		score += 2*self.numberBGPRoutersScore()
		#score += 2*self.domainSizeDeviationScore()

		start_t = time.time()
		if self.MCMCIter % 100 == 0 : 
			confScore = self.configurationScore()
			self.prevConfScore = confScore
		else : 
			confScore = self.prevConfScore + self.findConfScoreDiff(sw, oldDomain, newDomain)
			self.prevConfScore = confScore
		self.confScoreTime += time.time() - start_t
		if confScore > self.worstConfScore : 
			self.worstConfScore = confScore
		if confScore < self.bestConfScore : 
			self.bestConfScore = confScore
		
		score += confScore

		start_t = time.time()
		rfScore = self.routeFilterScore()
		self.rfScoreTime = time.time() - start_t
		if rfScore > self.worstRFScore : 
			self.worstRFScore = rfScore
			self.worstDomainAssigmentRF = copy.deepcopy(self.switchDomains) # Copy the worst RF domain assignment.
		if rfScore < self.bestRFScore : 
			self.bestRFScore = rfScore

		score += 0.025*rfScore

		return score

	def domainSizeScore(self) : 
		# compute domain size (if in range or not).
		score = 0 
		
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

		# State resets
		for subnet in self.destinationDAGs.keys() :
			for domain in range(self.numDomains) : 
				self.bgpRouterCounts[domain][subnet] = 0
 
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

			# Find largest non-loop path
			if len(aspath) == 1 : 
				# The entire path is the same domain, there is no BGP configuration required for this path
				self.lastNonLoopDownstreamPosition[pc] = -1
			else : 
				# Find longest path from destination which does not contain loops
				i = len(aspath) - 1
				lastNonLoopDownstreamPosition = -1
				while i > 0:
					domain = aspath[i]
					if aspath.count(domain) > 1 : 
						# Domain part of loop.
						for j in range(i - 1, -1, -1) :
							if aspath[j] == domain :
								# First repitition from the end. 
								if j > lastNonLoopDownstreamPosition :
									lastNonLoopDownstreamPosition = j
					i -= 1
				self.lastNonLoopDownstreamPosition[pc] = lastNonLoopDownstreamPosition

		score = 0
		for pc in self.paths.keys() :
			score += self.findStaticConfScore(pc, self.paths[pc], self.ASPaths[pc], self.ASPositions[pc], self.lastNonLoopDownstreamPosition[pc])

		# Precompute Shortest AS Paths
		for domain1 in range(self.numDomains) :
			for domain2 in range(self.numDomains) :
				if domain1 == domain2 : continue

				[uniqueness, shortestASPath] = self.findShortestASPath(domain1, domain2)
				if uniqueness : 
					self.shortestASPaths[domain1][domain2] = shortestASPath
				else : 
					self.shortestASPaths[domain1][domain2] = []

		for domain in range(self.numDomains) : 
			for subnet in self.destinationDAGs.keys() : 
				domainpaths = dict()
				nexthopAS = dict()
				for pc in self.paths.keys() :
					if subnet != self.pdb.getDestinationSubnet(pc) : continue

					# Find domain in path
					index = -1
					path = self.paths[pc]
					aspath = self.ASPaths[pc]
					aspositions = self.ASPositions[pc]
					for j in range(self.lastNonLoopDownstreamPosition[pc] + 1, len(aspath)) : 
						if aspath[j] == domain : 
							index = j
						break
					
					if index == len(aspath) - 1 or index < 0: 
						continue # No local preferences required
					else :
						domainpath = path[aspositions[index]:aspositions[index + 1]] # Extracts the path in the domain.

					if domainpath == [] : 
						print "Something", path, index, aspath, aspositions
						exit(0)
					
					domainpaths[pc] = domainpath
					nexthopAS[pc] = aspath[index+1]

				for sw in self.destinationDAGs[subnet] :
					if self.destinationDAGs[subnet][sw] == None : 
						dstDomain = self.switchDomains[sw]
						[localPrefScore, bgpRouterCount] = self.findLocalPrefScore(domain, dstDomain, domainpaths, nexthopAS) 
						self.bgpRouterCounts[domain][subnet] = bgpRouterCount
						score += localPrefScore
						break

		return score

	def findStaticConfScore(self, pc, path, aspath, aspositions, lastNonLoopDownstreamPosition) :
		""" Find conf score for a single path """
		src = path[0]
		dst = path[len(path) - 1]

		score = 0

		if len(aspath) == 1 : 
			# The entire path is the same domain, there is no BGP configuration required for this path
			score += 0

		else : 
			if lastNonLoopDownstreamPosition > -1 : 
				# A looped path. Add static routing till start of (lastNonLoopDownstreamPosition + 1)th AS
				# Routing from (lastNonLoopDownstreamPosition + 1)th AS to destination is loop-free
				posSw = aspositions[lastNonLoopDownstreamPosition + 1] 
				
				# Static routing cost is the number of rules required till posSw
				score += posSw

		return score

	def findLocalPrefScore(self, domain, dstDomain, domainpaths, nexthopAS) : 
		if domain == dstDomain : 
			return [0,0] # Dont need local prefs

		shortestASPath = self.shortestASPaths[domain][dstDomain]
		if shortestASPath == [] :
			uniqueness = False
		else :
			uniqueness = True

		score = 0
		bgpRouterCount = 0
		if uniqueness and len(domainpaths) == 1 :
			for pc in domainpaths.keys() :
				if nexthopAS[pc] == shortestASPath[1] : 
					# next hop AS is on unique shortest path
					# Dont need local prefs
					score += 0

		else : 
			# Find number of bgp routers = B
			bgpRouters = []
			for dp in domainpaths.values() : 
				if dp[len(dp) - 1] not in bgpRouters : 
					bgpRouters.append(dp[len(dp) - 1])

			# Require B local preference entries and B(B-1)/2 number of iBGP filters
			# to propagate eBGP routes inside the OSPF domain.
			score += len(bgpRouters)*(len(bgpRouters) + 1)*0.5
			bgpRouterCount = len(bgpRouters)
		
		return [score, bgpRouterCount]

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
			oldlastNonLoopDownstreamPosition = self.lastNonLoopDownstreamPosition[pc]

			# Compute old static score.
			oldScore = self.findStaticConfScore(pc, path, oldaspath, oldaspositions, oldlastNonLoopDownstreamPosition)

			newaspath = [self.switchDomains[src]]
			newaspositions = [0] # Store the positions when the AS first starts.
			for i in range(1, len(path)) : 
				domain = self.switchDomains[path[i]]
				if domain != newaspath[len(newaspath) - 1] : 
					# Next AS. Add to AS path
					newaspath.append(domain)
					newaspositions.append(i)

			# Find largest non-loop path
			if len(newaspath) == 1 : 
				# The entire path is the same domain, there is no BGP configuration required for this path
				newlastNonLoopDownstreamPosition = -1
			else : 
				# Find longest path from destination which does not contain loops
				i = len(newaspath) - 1
				newlastNonLoopDownstreamPosition = -1
				while i > 0:
					domain = newaspath[i]
					if newaspath.count(domain) > 1 : 
						# Domain part of loop.
						for j in range(i - 1, -1, -1) :
							if newaspath[j] == domain :
								# First repitition from the end. 
								if j > newlastNonLoopDownstreamPosition :
									newlastNonLoopDownstreamPosition = j
					i -= 1

			newscore = self.findStaticConfScore(pc, path, newaspath, newaspositions, newlastNonLoopDownstreamPosition)

			scoreDiff = scoreDiff - oldScore + newScore

			# Check to see if sw is not staticly routed.
			swIndex = path.index(sw)
			if swIndex < oldaspositions[oldlastNonLoopDownstreamPosition + 1] :
				# sw statically routed. No change in local pref scores
				continue

			# Find local pref difference
			if len(oldaspath) == len(newaspath) :
				# sw just moved across the domains, no change in local prefs
				scoreDiff += 0
			elif len(oldaspath) == len(newaspath) + 1 :
				# new AS path has reduced length. Decrement oldDomain's local pref entries
				scoreDiff -= self.bgpRouterCounts[oldDomain][self.pdb.getDestinationSubnet(pc)]
			elif len(oldaspath) + 1 == len(newaspath) :
				# new AS path has increased length. Increment newDomain's local pref entries
				scoreDiff += self.bgpRouterCounts[newDomain][self.pdb.getDestinationSubnet(pc)] + 1


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

						boundary1 = self.boundarySwitches[aspath[0]]
						boundary2 = self.boundarySwitches[aspath[1]]

						linkCount = 0 # Denotes the number of links connecting domains 1 & 2
						for sw in boundary1 : 
							neighbours = self.topologyNeighbours[sw]
							for n in neighbours : 
								if n in boundary2 : 
									linkCount += 1 # AS1-AS2 link

						if linkCount == 1:
							return [True, aspath]
						else : 
							return [False, None]

				# Find neighbouring domains
				neighbouringDomains = []
				boundary = self.boundarySwitches[d]
				for sw in boundary :
					for n in self.topologyNeighbours[sw] :
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
		dsts = self.pdb.getDestinationSubnets()
		
		self.diamondCount = [[0 for x in range(self.swCount + 1)] for x in range(self.swCount + 1)]
		self.diamondPaths = [[[] for x in range(self.swCount + 1)] for x in range(self.swCount + 1)]
		
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
									self.diamondCount[swDiv][swConv] += 1
									dstpath1 = dstpath1[:dstpath1.index(swConv) + 1]
									if dstpath1 not in self.diamondPaths[swDiv][swConv] :
										self.diamondPaths[swDiv][swConv].append(dstpath1)

									dstpath2 = dstpath2[:dstpath2.index(swConv) + 1]
									if dstpath2 not in self.diamondPaths[swDiv][swConv] :
										self.diamondPaths[swDiv][swConv].append(dstpath2)
									break


	def routeFilterScore(self) :
		# Score based on number of OSPF filters required in each domain.
		# This is overapproximated by number of diamonds in each domain.

		score = 0
		for domain in range(self.numDomains) :
			for sw1 in self.domains[domain] : 
				for sw2 in self.domains[domain] :
					if self.diamondCount[sw1][sw2] > 0 : 
						# There are diamonds in the domain. Check if paths stay in domain or not.
						domainPathCount = 0
						for path in self.diamondPaths[sw1][sw2] : 
							inDomain = True
							for sw in path : 
								if self.switchDomains[sw] != domain : 
									inDomain = False 
									break
							if inDomain :
								domainPathCount += 1

						# There are $n$ paths inside the domain which converge. Require atmost n*n-1*0.5 rfs
						score += self.diamondCount[sw1][sw2] + (domainPathCount * (domainPathCount - 1) * 0.5) 

		return score

	# def calibrateFilterScore(self) : 
	# 	# The RF score computed by number of diamonds is a greater over-approximation.
	# 	# Find number of filters and try to find the correlation factor between diamonds and RF count.
		
	# 	self.computeRandomDomainAssignment()
	# 	self.computeBoundaries() # boundary bookkeeping for efficiency 

	# 	rfScore = self.routeFilterScore()
	# 	RFCount = self.synthesizeOSPFConfigurations()
	# 	rfFactor = float(rfScore)/float(RFCount)

	# 	# Repeat again
	# 	self.computeRandomDomainAssignment()
	# 	self.computeBoundaries() # boundary bookkeeping for efficiency 

	# 	rfScore2 = self.routeFilterScore()
	# 	RFCount2 = self.synthesizeOSPFConfigurations()
	# 	rfFactor2 = float(rfScore2)/float(RFCount2)

	# 	print rfFactor, rfFactor2
	# 	exit(0)


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


	def getDomainTopology(self, domain, switchDomains=None) :
		""" Constructs the topology object for domain"""
		topo = Topology(name="domain"+str(domain))

		if switchDomains == None :
			switchDomains = self.switchDomains

		for sw in range(1,self.swCount+1) :
			if switchDomains[sw] != domain : continue # sw not in domain
			domainNeighbours = []
			for n in self.topologyNeighbours[sw] :
				if switchDomains[n] == domain : 
					domainNeighbours.append(self.topology.getSwName(n))
			topo.addSwitch(self.topology.getSwName(sw), domainNeighbours)
			
		return topo

	def getDomainDAGs(self, domain, pdb, topology, switchDomains=None) : 
		""" Returns DAGs, endpoints and bgpExtensions for domain. Side-effect: Sets up pdb with the paths """
		
		if switchDomains == None :
			switchDomains = self.switchDomains

		dags = dict()
		endpoints = []

		for pc in self.paths.keys() : 
			path = self.paths[pc]
			src = path[0]
			dst = path[len(path) - 1]

			aspath = [switchDomains[src]]
			aspositions = [0] # Store the positions when the AS first starts.
			for i in range(1, len(path)) : 
				d = switchDomains[path[i]]
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
				lastNonLoopDownstreamPosition = -1
				while i > 0:
					d = aspath[i]
					if aspath.count(d) > 1 : 
						# Domain part of loop.
						for j in range(i - 1, -1, -1) :
							if aspath[j] == d :
								# First repitition from the end. 
								if j > lastNonLoopDownstreamPosition :
									lastNonLoopDownstreamPosition = j
					i -= 1

				# A looped path. Add static routing till start of (lastNonLoopDownstreamPosition + 1)th AS
				# Routing from (lastNonLoopDownstreamPosition + 1)th AS to destination is loop-free
				index = -1
				for j in range(lastNonLoopDownstreamPosition + 1, len(aspath)) : 
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
						topopath.append(topology.getSwID(self.topology.getSwName(sw)))

					if len(topopath) > 1 : 
						# If len == 1, then path will not use OSPF
						subnet = self.pdb.getDestinationSubnet(pc)
						dpc = pdb.addReachabilityPolicy(subnet, topopath[0], topopath[len(topopath) - 1])
						pdb.addPath(dpc, topopath)
						endpoints.append([topopath[0], subnet])

						# print aspath, lastNonLoopDownstreamPosition, path, self.pdb.getDestinationSubnet(pc), domainpath
						# Add path to Dag of subnet
						if subnet not in dags :
							dags[subnet] = dict()
						
						dags[subnet][topopath[len(topopath) - 1]] = None
						for i in range(len(topopath) - 1) :
							dags[subnet][topopath[i]] = topopath[i + 1]
		
		bgpExtensions = []
		# Find BGP extensions
		for subnet in dags : 
			bgpRouters = []
			dag = dags[subnet]
			# extract the bgp routers. 
			for sw in dag : 
				if dag[sw] == None : 
					bgpRouters.append(sw)

			if len(bgpRouters) > 1 :
				# More than one endpoint. 
				for pc in range(pdb.getPacketClassRange()) : 
					if pdb.getDestinationSubnet(pc) == subnet : 
						for bgpr in bgpRouters : 
							if bgpr != pdb.getDestinationSwitch(pc) : 
								bgpExtensions.append([pdb.getSourceSwitch(pc), pdb.getDestinationSwitch(pc), bgpr, subnet])

		pdb.addBGPExtensions(bgpExtensions)
		# print dags
		return [dags, endpoints, bgpExtensions]
		

	def synthesizeOSPFConfigurations(self, switchDomains=None) : 
		# Found a domain assignment from MCMC. Solve the OSPF domains now.
		RFCount = 0
		for domain in range(self.numDomains) :
			topo = self.getDomainTopology(domain, switchDomains)

			pdb = PolicyDatabase()
			print "domain", domain
			[dags, endpoints, bgpExtensions] = self.getDomainDAGs(domain, pdb, topo, switchDomains)

			for dst in dags : 
				pdb.addDestinationDAG(dst, dags[dst])

			zepSynthesiser = ZeppelinSynthesiser(topo, pdb)
			routeFilters = zepSynthesiser.enforceDAGs(dags, endpoints, bgpExtensions)

			for dst in routeFilters : 
				RFCount += len(routeFilters[dst])

		print "Number of route filters are ", RFCount
		return RFCount

