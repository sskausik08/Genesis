from GPLInterpreter import GPLInterpreter
from Topology import Topology
from GenesisSynthesiser import GenesisSynthesiser
import sys

class Genesis(object):
    def __init__(self) :
        if not len(sys.argv) == 2 :
            print "Usage : python PolicyCompiler.py <name--of-configuration-file>"
            exit(0)

        self.topology = Topology()
        self.genesisSynthesiser = GenesisSynthesiser(self.topology)
        self.parser = GPLInterpreter(sys.argv[1], self.genesisSynthesiser)
        
    def run(self):
        self.parser.run()
        self.genesisSynthesiser.enforcePolicies()

genesis = Genesis()
genesis.run()