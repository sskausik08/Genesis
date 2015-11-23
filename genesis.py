"""
Genesis : Endpoint Policy Enforcement using Flow Table Synthesis
"""

from GPLInterpreter import GPLInterpreter
from Topology import Topology
from GenesisSynthesiser import GenesisSynthesiser
import sys

class Genesis(object):
	# """
	# The Genesis class : contains an interpreter for GPL and the synthesiser.  
	# """
    def __init__(self) :
    	"""
        Construct a new Genesis object.
        """
        if not len(sys.argv) == 2 :
            print "Usage : python PolicyCompiler.py <name--of-configuration-file>"
            exit(0)

        self.topology = Topology()
        self.genesisSynthesiser = GenesisSynthesiser(topo=self.topology, fuzzy=False)
        self.parser = GPLInterpreter(sys.argv[1], self.genesisSynthesiser, self.topology)
        
    def run(self):
        self.parser.run()
        #self.genesisSynthesiser.addPolicies()
        self.genesisSynthesiser.enforcePolicies()

        while True:
	        s = raw_input('--> ') 
	        if len(s) == 0:
	        	continue
	        fields = s.split()
	    	if fields[0] == "change" and len(fields[1]) > 0:
	    		gplfile = open(fields[1])
	    		gpl = gplfile.read()
	    		self.parser.parseGPL(gpl)
	    		#newpc = self.genesisSynthesiser.addReachabilityPolicy("10.0.0.2", "s1", "10.0.0.8", "s5", ["s9"])
        		#self.genesisSynthesiser.addTrafficIsolationPolicy(0, newpc)
	    		self.genesisSynthesiser.enforceChangedPolicies()
	    	elif fields[0] == "exit" :
	    		break

        
        
        

    # Add API support.
    def addReachPolicy(self, srcIP, srcSw, dstIP, dstSw):
    	"""
    	Add a reachabilty policy between two endpoints. 

    	:param srcIP: The source IP address/subnet.
		:param srcSw: The OpenFlow switch connected to the source. 
		:param dstIP: The destination IP address/subnet.
		:param dstSw: The OpenFlow switch connected to the destination. 
		:return: returns the policy number. This can be used to specify isolation policies for this flow.
        """
    	pass

    def addReachWaypointPolicy(self, srcIP, srcSw, dstIP, dstSw, waypoints):
    	pass

    def addTrafficIsolationPolicy(self, policy1, policy2):
    	pass

    def addSwitch(self, sw, neighbours):
    	pass

    def addSwitchTableConstraint(self, sw, maxTableSize):
    	pass



genesis = Genesis()
genesis.run()