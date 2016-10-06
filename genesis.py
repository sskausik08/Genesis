"""
Genesis : Endpoint Policy Enforcement using Flow Table Synthesis
"""

from GPLInterpreter import GPLInterpreter
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from GenesisSynthesiser import GenesisSynthesiser
#from GenesisILPSynthesiser import GenesisILPSynthesiser
import sys

class Genesis(object):
	# """
	# The Genesis class : contains an interpreter for GPL and the synthesiser.  
	# """
	def __init__(self) :
		"""
		Construct a new Genesis object.
		"""
		# Parse the command line arguments
		no = 0
		gplargFlag = False
		topoargFlag = False
		DCFlag = False # Default DC flag is false.
		TopoSlicingFlag = False # Default Topology Slicing flag is flag
		UseTacticFlag = False
		NoOptimizationsFlag = False
		WeakIsolationFlag = False
		useILPFlag = False
		generateControlPlaneFlag = False
		repairMode = False

		for arg in sys.argv : 
			if arg == "-gpl" :
				self.gplfile = sys.argv[no + 1]
				gplargFlag = True
			if arg == "-topo" :
				self.topofile = sys.argv[no + 1]
				topoargFlag = True
			if arg == "-dc" :
				DCFlag = True
			if arg == "-useTactic" :
				UseTacticFlag = True
			if arg == "-noOpt" : 
				NoOptimizationsFlag = True
			if arg == "wi" :
				WeakIsolationFlag = True
			if arg == "-repair" : 
				repairMode = True
			if arg == "-c3" :
				generateControlPlaneFlag = True
			no += 1

		if not (gplargFlag and topoargFlag) : 
			print "GPL and Topology arguments not specified"
			exit(0)


		self.topology = Topology()
		self.policyDatabase = PolicyDatabase()
		if not useILPFlag : 
			self.genesisSynthesiser = GenesisSynthesiser(topo=self.topology, pdb=self.policyDatabase, DC=DCFlag, TopoSlicing=TopoSlicingFlag, useTactic=UseTacticFlag, noOptimizations=NoOptimizationsFlag, weakIsolation=WeakIsolationFlag, repairMode=repairMode, controlPlane=generateControlPlaneFlag)
		else : #ignore
			self.genesisSynthesiser = GenesisILPSynthesiser(topo=self.topology, DC=DCFlag, TopoSlicing=TopoSlicingFlag, useTactic=UseTacticFlag, noOptimizations=NoOptimizationsFlag, weakIsolation=WeakIsolationFlag)
		self.gplparser = GPLInterpreter(self.gplfile, self.topofile, self.genesisSynthesiser, self.topology)
		
	def run(self):
		self.gplparser.parseTopo()
		self.gplparser.parseGPL()
		self.genesisSynthesiser.enforcePolicies()

		exit(0)
		# while True:
		# 	s = raw_input('--> ') 
		# 	if len(s) == 0:
		# 		continue
		# 	fields = s.split()
		# 	if fields[0] == "c" and len(fields[1]) > 0:
		# 		gplfile = open(fields[1])
		# 		gpl = gplfile.read()
		# 		self.parser.parseGPL(gpl)
		# 		#newpc = self.genesisSynthesiser.addReachabilityPolicy("10.0.0.2", "s1", "10.0.0.8", "s5", ["s9"])
		# 		#self.genesisSynthesiser.addTrafficIsolationPolicy(0, newpc)
		# 		#self.genesisSynthesiser.enforceChangedPolicies()
		# 	elif fields[0] == "ex" :
		# 		break


genesis = Genesis()
genesis.run()