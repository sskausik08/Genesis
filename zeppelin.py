"""
Zeppelin : ARC Synthesis from Data planes
"""

from GPLInterpreter import GPLInterpreter
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from ZeppelinSynthesiser import ZeppelinSynthesiser
from OuterZeppelinSynthesiser import OuterZeppelinSynthesiser
from ZeppelinInputGenerator import ZeppelinInputGenerator
import sys

class Zeppelin(object):
	# """
	# The Zeppelin class : contains an interpreter for GPL and the synthesiser.  
	# """
	def __init__(self) :
		"""
		Construct a new Zeppelin object.
		"""
		# Parse the command line arguments
		self.pcRange = 10 # default
		self.subnets = 10 
		no = 0
		self.topoargFlag = False
		self.ospfFlag = False
		self.timeout = 300
		self.distance = 10
		self.numDomains = 5
		for arg in sys.argv : 
			if arg == "-topo" :
				self.topofile = sys.argv[no + 1]
				self.topoargFlag = True
			if arg == "-pc" :
				self.pcRange = int(sys.argv[no + 1])
			if arg == "-subnets" :
				self.subnets = int(sys.argv[no + 1])
			if arg == "-ospf" : 
				self.ospfFlag = True # Synthesize a single ospf domain.
			if arg == "-to" :
				self.timeout = int(sys.argv[no + 1])
			if arg == "-dist" :
				self.distance = int(sys.argv[no + 1])
			if arg == "-domains" : 
				self.numDomains = int(sys.argv[no + 1])

			no += 1

		if not self.topoargFlag : 
			print "Topology arguments not specified"
			exit(0)

		self.topology = Topology()
		self.policyDatabase = PolicyDatabase()
		self.gplparser = GPLInterpreter(self.topofile, self.topofile, None, self.topology)
		
	def run(self):
		self.gplparser.parseTopo()
		self.zepInput = ZeppelinInputGenerator(self.topology, self.policyDatabase, self.pcRange, self.subnets, self.distance)
			
		if self.ospfFlag : 
			# Synthesize a single OSPF domain.
			self.zepSynthesiser = ZeppelinSynthesiser(self.topology, self.policyDatabase)
			self.zepSynthesiser.enforceDAGs(self.zepInput.getDestinationDAGs(), self.zepInput.getEndpoints())

		else : 
			self.outerZepSynthesizer = OuterZeppelinSynthesiser(topology=self.topology, pdb=self.policyDatabase, timeout=self.timeout, numDomains=self.numDomains)
			self.outerZepSynthesizer.enforceDAGs(self.zepInput.getDestinationDAGs(), self.zepInput.getPaths(), self.zepInput.getEndpoints())
	

zep = Zeppelin()
zep.run()