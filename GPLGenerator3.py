from Topology import Topology
from GPLInterpreter import GPLInterpreter
import sys
import random
import math

# python GPLGenerator.py <topology-file> <number-of-packet-classes> <tenant-group-size> <gpl-filename>
# python GPLGenerator.py ./topologies/fattree-6.topo 50 10 fat6-50-10.gpl
if len(sys.argv) <> 5 : 
	print "python GPLGenerator.py <topology-file> <number-of-packet-classes> <te> <gpl-filename>"
	exit(0)
topoFile = sys.argv[1]
count = int(sys.argv[2])
te = sys.argv[3]
gplfile = open(sys.argv[4], 'w')

topology = Topology()
gplparser = GPLInterpreter(topoFile, topoFile, None, topology)
gplparser.parseTopo()


swCount = topology.getSwitchCount()
edgeSwitches = (topology.getSwitchCount() * 2/ 5) - 1  
k = int(math.sqrt(topology.getSwitchCount() * 4/ 5))

groups = 1
groupsize = count
srcCount = dict()
dstCount = dict()
for i in range(edgeSwitches + 1) :
	srcCount[i] = 0
	dstCount[i] = 0
endpoints = dict()
for i in range(groups) :
	for j in range(groupsize) :
		while True:		
			s = random.randint(0,edgeSwitches)
			d = random.randint(0,edgeSwitches)
			a = random.randint(edgeSwitches + 1, swCount - 1)
			if s <> d :
				if s > d : 
					key = str(d) + "-" + str(s)
				else :
					key = str(s) + "-" + str(d)
				if key not in endpoints : 
					if srcCount[s] < k/2 and dstCount[d] < k/2 :
						endpoints[key] = True
						srcCount[s] += 1
						dstCount[d] += 1
						break			

		gplfile.write("p" + str(i) + "_" + str(j) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> e" + str(d) + "\n")

gplfile.write("== \n")	
if te == "minimize-avg-te" : 
	# minimize average util
	gplfile.write("minimize-avg-te \n")	
elif te == "minimize-max-te" : 
	# minimize max util
	gplfile.write("minimize-max-te \n")	


