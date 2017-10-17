from Topology import Topology
from GPLInterpreter import GPLInterpreter
import sys
import random
import math

# python GPLGenerator.py <topology-file> <number-of-packet-classes> <tenant-group-size> <gpl-filename>
# python GPLGenerator.py ./topologies/fattree-6.topo 50 10 fat6-50-10.gpl
if len(sys.argv) <> 5 : 
	print "python GPLGenerator.py <topology-file> <number-of-packet-classes> <tenant-group-size> <gpl-filename>"
	exit(0)
topoFile = sys.argv[1]
count = int(sys.argv[2])
isolatePercentage = int(sys.argv[3])
gplfile = open(sys.argv[4], 'w')

topology = Topology()
gplparser = GPLInterpreter(topoFile, topoFile, None, topology)
gplparser.parseTopo()


swCount = topology.getSwitchCount()
edgeSwitches = (topology.getSwitchCount() * 2/ 5) - 1  
k = int(math.sqrt(topology.getSwitchCount() * 4/ 5))

groups = count / isolatePercentage
groupsize = isolatePercentage
srcCount = dict()
dstCount = dict()
for i in range(edgeSwitches + 1) :
	srcCount[i] = 0
	dstCount[i] = 0
endpoints = dict()
currdst = 0
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

		gplfile.write("p" + str(i) + "_" + str(j) + " := "  + str(currdst) + " : e" + str(s)  + " >> e" + str(d) + "\n")
		currdst += 1

if groups == 1 : # If no of packet classes = group size, then there are no isolation policies
	exit(0)
gplfile.write("== \n")	
sets = dict()
for i in range(groups) :
	set = "[ "
	for j in range(groupsize) :
		set += "p" + str(i) + "_" + str(j)
		if j <> groupsize - 1: 
			set += ", "
	set += " ]"
	sets[i] = set

for i in range(groups) :
	for j in range(i) :
		if i <> j : 
			gplfile.write(sets[i] + " || " + sets[j] + "\n")



