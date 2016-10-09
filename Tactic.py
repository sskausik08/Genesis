from FAdo.fa import *
from FAdo.reex import *
from z3 import If
from Topology import Topology


# class Regex(object):
# 	""" Regex class built using FAdo.reex which of regexStr """
# 	def __init__(self, regexStr, sigma, isNeg=False) :
# 		self.sigma = sigma
# 		self.regex = str2regexp(s=self.preprocessDot(regexStr), sigma=self.sigma)
# 		self.isNegated = isNeg
# 		if self.isNegated : 
# 			self.dfa = self.regex.nfaPosition().toDFA().minimal(complete=False)
# 			self.dfa = ~self.dfa
# 			self.dfa = self.dfa.toDFA().minimal(complete=False)

# 		else : 
# 			self.dfa = self.regex.nfaPosition().toDFA().minimal(complete=False)

# 	def preprocessDot(self, regexStr) :
# 		""" Convert dot to disjunction of all elements in sigma """
# 		dotStr = "("
# 		for i in range(len(self.sigma) - 1) : 
# 			dotStr += self.sigma[i] + "+"
# 		dotStr += self.sigma[len(self.sigma) - 1] + ")"
# 		return string.replace(regexStr, ".", dotStr)

# 	def getDFA(self) :
# 		return self.dfa


# class Blacklist(Regex) :
# 	""" Blacklist class to denote tactics which satisfy the negation of the regex"""
# 	def __init__(self, regex, sigma):
# 		Regex.__init__(self, regex, sigma, True)

# class Whitelist(Regex) :
# 	""" Blacklist class to denote tactics which satisfy the regex"""
# 	def __init__(self, regex, sigma):
# 		Regex.__init__(self, regex, sigma, False)

# Follows the grammar specified in the Genesis POPL paper
class TacticRegex(object): 
	def __init__(self, l_src, l_dst, tlen, l1="", l2=""): 
		self.l_src = l_src
		self.l_dst = l_dst
		self.tlen = tlen
		self.l1 = l1 # "" = epsilon
		self.l2 = l2 # "" = epsilon


class Tactic(object):
	def __init__(self, sigma, regexList, topology) :
		""" Tactic satisfies all the restricted regular expressions in regexList"""
		self.sigma = sigma
		self.labelMappings = dict()
		# Map sigma to integers.
		i = 0
		for lb in self.sigma : 
			self.labelMappings[lb] = i
			i += 1

		self.topology = topology
		maxPathLen = self.topology.getMaxPathLength()

		# Computing previous neighbour information. Will be pruned using the tactics and used when generating the constraints
		self.neighbours = dict()
		for lb in self.sigma :
			self.neighbours[lb] = dict()
			for i in range(1, maxPathLen + 1):
				self.neighbours[lb][i] = self.sigma

		if len(regexList) == 0 :
			print "Cannot create empty Tactic. Exit"
			exit(0)
		

		for tregex in regexList : 
			if tregex.l1 == "" and tregex.l2 == "" :
				# Tactic of the form: not (l_src .^i .^* l_dst) =>
				# Restricts the path to a length < i + 1
				for lb in self.sigma : 
					for i in range(tregex.tlen + 1, maxPathLen + 1):
						self.neighbours[lb][i] = [] # Prune all constraints for Reach at length i for all switches of lb

			elif tregex.l2 == "":
				# Tactic of the form: not (l_src .^i l .^* l_dst) =>
				# a switch with label l cannot be reached in i + 1 steps, except if switch is the detination
				self.neighbours[tregex.l1][tregex.tlen + 1] = ["!DST!"] # Check special destination case before pruning

			else : 
				# Tactic of the form: not (l_src .^i l_1 l_2 .^* l_dst) => 
				# This tactic ensures that a switch with label l_1 at i + 1 in the path
				# will not forward the packet to a switch with label l_2 
				neighbours = self.neighbours[tregex.l2][tregex.tlen + 2] 
				newNeighbours = []
				for lb in neighbours : 
					if lb != tregex.l1 : 
						newNeighbours.append(lb)
				
				self.neighbours[tregex.l2][tregex.tlen + 2] = newNeighbours


	def getPreviousLabels(self, label, Reach) :
		return self.neighbours[label][Reach]

		# self.dfa = regexList[0].getDFA()
		# for i in range(1, len(regexList)) :
		# 	self.dfa = self.dfa & regexList[i].getDFA()
		# 	self.dfa = self.dfa.minimalHopcroft()

		# self.dfa.completeMinimal()
		# self.numStates = len(self.dfa.States)
		# self.dfa.renameStates(range(self.numStates))

		# self.sigma = regexList[0].sigma
		# self.topology = topology
		

		# self.sink = None

	# def getDFA(self):
	# 	return self.dfa

	# def getSinkState(self) :
	# 	return self.sink

	# def computeSinkState(self) :
	# 	for s in range(self.numStates) :
	# 		isSink = True
	# 		transitions = self.dfa.delta[s]
	# 		for lb in transitions.keys() : 
	# 			if transitions[lb] <> s :
	# 				# Not a self-loop
	# 				isSink = False
	# 		if isSink :
	# 			# Check if accepting. If not, we are done.
	# 			if s not in self.dfa.Final :
	# 				# this is sink state. Since automata is minimal, we only have one sink state.
	# 				self.sink = s
	# 				return s

	# 	return -1

	# def getDelta(self) :
	# 	""" Return transition function as a tuple of [s, label, nexts] """
	# 	delta = []
	# 	for s in range(self.numStates) :
	# 		transitions = self.dfa.delta[s]
	# 		for lb in transitions.keys() : 
	# 			delta.append([s, self.labelMappings[lb], transitions[lb]])
	# 	return delta

	# def getLabelMapping(self, label) :
	# 	""" Converts label to mapped int"""
	# 	return self.labelMappings[label]

	# def getSwitchLabelMapping(self, sw) :
	# 	""" Converts switch to mapped int"""
	# 	label = self.topology.getLabel(sw)
	# 	return self.labelMappings[label]

	# def getFinalStates(self) :
	# 	return self.dfa.Final

	# def getInitialState(self) :
	# 	return self.dfa.Initial

	# def findValidNeighbours(self, plen):
	# 	""" Generate non-sink paths of plen length to find valid previous neighbours """
	# 	# Compute sink.
	# 	self.computeSinkState()

	# 	self.paths = dict()
	# 	for i in range(1, plen + 1):
	# 		self.paths[i] = []

	# 	self.neighbours = dict()
	# 	for lb in self.sigma :
	# 		self.neighbours[lb] = dict()
	# 		for i in range(2, plen + 1):
	# 			self.neighbours[lb][i] = []

	# 	def getPathsHelper(plen) :
	# 		paths = self.paths[plen - 1]
	# 		# Each path in paths will be of the form [lastlabel, final-state]
	# 		for path in paths : 
	# 			lastlabel = path[0]
	# 			state = path[1]
	# 			transitions = self.dfa.delta[state]

	# 			for lb in transitions.keys() :
	# 				newstate = transitions[lb]
	# 				if newstate == self.sink :
	# 					continue
	# 				if not self.topology.isLabelConnected(lastlabel, lb):
	# 					continue
	# 				# add last-label to neighbours.
	# 				if lastlabel not in self.neighbours[lb][plen] :
	# 					self.neighbours[lb][plen].append(lastlabel)

	# 				self.paths[plen].append([lb, newstate])

	# 	# Compute paths of len 1.
	# 	transitions = self.dfa.delta[self.dfa.Initial]
	# 	for lb in transitions.keys() :
	# 		lastlabel = lb
	# 		newstate = transitions[lb]
	# 		if newstate == self.sink :
	# 			continue
	# 		self.paths[1].append([lastlabel, newstate])

	# 	for l in range(2, plen + 1):
	# 		getPathsHelper(l)









		










# b1 = Blacklist("e .* e .* e", ["a","c","e"])
# b2 = Blacklist(".* a .* c .* a .* c .* a .*", ["a","c","e"])

# t = Tactic([b1])
# t.getPaths(10)
# print t.getDFA().delta
# print t.getDFA().Final
# print t.getSinkState()
