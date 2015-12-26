from FAdo.fa import *
from FAdo.reex import *
from z3 import If
from Topology import Topology


class Regex(object):
	""" Regex class built using FAdo.reex which stores reverse of regexStr """
	def __init__(self, regexStr, sigma, isNeg=False) :
		self.sigma = sigma
		self.regex = str2regexp(s=self.preprocessDot(regexStr), sigma=self.sigma)
		self.isNegated = isNeg
		print self.regex
		if self.isNegated : 
			self.dfa = self.regex.nfaPosition().reversal().toDFA().minimal(complete=False)
			self.dfa = ~self.dfa
		else : 
			self.dfa = self.regex.nfaPosition().reversal().toDFA().minimal(complete=False)

	def preprocessDot(self, regexStr) :
		""" Convert dot to disjunction of all elements in sigma """
		dotStr = "("
		for i in range(len(self.sigma) - 1) : 
			dotStr += self.sigma[i] + "+"
		dotStr += self.sigma[len(self.sigma) - 1] + ")"
		return string.replace(regexStr, ".", dotStr)

	def getDFA(self) :
		return self.dfa


class Blacklist(Regex) :
	""" Blacklist class to denote tactics which satisfy the negation of the regex"""
	def __init__(self, regex, sigma):
		Regex.__init__(self, regex, sigma, True)

class Whitelist(Regex) :
	""" Blacklist class to denote tactics which satisfy the regex"""
	def __init__(self, regex, sigma):
		Regex.__init__(self, regex, sigma, False)

class Tactic(object):
	def __init__(self, regexList, topology) :
		""" Tactic satisfies all the regular expressions in regexList. 
		regexList contains the list of blacklists and whitelists"""
		if len(regexList) == 0 :
			print "Cannot create empty Tactic. Exit"
			exit(0)
		self.dfa = regexList[0].getDFA()
		for i in range(1, len(regexList)) :
			self.dfa = self.dfa & regexList[i].getDFA()
			self.dfa = self.dfa.minimalHopcroft()

		self.dfa.completeMinimal()
		self.numStates = len(self.dfa.States)
		self.dfa.renameStates(range(self.numStates))

		self.sigma = regexList[0].sigma
		self.topology = topology
		self.labelMappings = dict()
		# Map sigma to integers.
		i = 0
		for lb in self.sigma : 
			self.labelMappings[lb] = i
			i += 1

	def getDFA(self):
		return self.dfa

	def getSinkState(self) :
		for s in range(self.numStates) :
			isSink = True
			transitions = self.dfa.delta[s]
			for lb in transitions.keys() : 
				if transitions[lb] <> s :
					# Not a self-loop
					isSink = False
			if isSink :
				# Check if accepting. If not, we are done.
				if s not in self.dfa.Final :
					# this is sink state. Since automata is minimal, we only have one sink state.
					return s

		return -1

	def getDelta(self) :
		""" Return transition function as a tuple of [s, label, nexts] """
		delta = []
		for s in range(self.numStates) :
			transitions = self.dfa.delta[s]
			for lb in transitions.keys() : 
				delta.append([s, self.labelMappings[lb], transitions[lb]])
		return delta

	def getLabelMapping(self, label) :
		""" Converts label to mapped int"""
		return self.labelMappings[label]

	def getSwitchLabelMapping(self, sw) :
		""" Converts switch to mapped int"""
		label = self.topology.getLabel(sw)
		return self.labelMappings[label]

	def getFinalStates(self) :
		return self.dfa.Final

	def getInitialState(self) :
		return self.dfa.Initial







# b1 = Blacklist(".* e .* e .* e .* ", ["a","c","e"])
# b2 = Blacklist(".* a .* c .* a .* c .* a .*", ["a","c","e"])

# t = Tactic([b1])
# print t.getDFA().delta
# print t.getDFA().Final
# print t.getSinkState()
