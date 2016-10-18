"""
Zeppelin : ARC Synthesis from Data planes
"""

from GPLInterpreter import GPLInterpreter
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from ZeppelinSynthesiser import ZeppelinSynthesiser
from OuterZeppelinSynthesiser import OuterZeppelinSynthesiser
from ZeppelinSynthesiser2 import ZeppelinSynthesiser2
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
		no = 0
		topoargFlag = False
		for arg in sys.argv : 
			if arg == "-topo" :
				self.topofile = sys.argv[no + 1]
				topoargFlag = True
			if arg == "-pc" :
				self.pcRange = int(sys.argv[no + 1])
			no += 1

		if not topoargFlag : 
			print "Topology arguments not specified"
			exit(0)


		self.topology = Topology()
		self.policyDatabase = PolicyDatabase()
		self.gplparser = GPLInterpreter(self.topofile, self.topofile, None, self.topology)
		
	def run(self):
		self.gplparser.parseTopo()
		self.zepInput = ZeppelinInputGenerator(self.topology, self.policyDatabase, self.pcRange)
		
		self.outerZepSynthesizer = OuterZeppelinSynthesiser(self.topology, self.policyDatabase)
		self.outerZepSynthesizer.enforceDAGs(self.zepInput.getDestinationDAGs(), self.zepInput.getPaths(), self.zepInput.getEndpoints())

		# exit(0)
		# self.zepSynthesiser = ZeppelinSynthesiser(self.topology, self.policyDatabase)
		# self.zepSynthesiser.enforceDAGs(self.zepInput.getDestinationDAGs(), self.zepInput.getEndpoints())

		# self.zepSynthesiser2 = ZeppelinSynthesiser(topology=self.topology, pdb=self.policyDatabase, minimalFilterSolve=True)
		# self.zepSynthesiser2.enforceDAGs(self.zepInput.getDestinationDAGs(), self.zepInput.getEndpoints())

		exit(0)



zep = Zeppelin()
zep.run()