from Topology import Topology
from GPLInterpreter import GPLInterpreter
import sys
import random
import math

# python GPLGenerator.py <topology-file> <number-of-packet-classes> <tenant-group-size> <gpl-filename>
# python GPLGenerator.py ./topologies/fattree-6.topo 50 10 fat6-50-10.gpl
if len(sys.argv) != 5 : 
	print "python GPLGenerator10.py <topology-file> <number-of-packet-classes> <number-of-waypoint-classes> <gpl-filename>"
	exit(0)
topoFile = sys.argv[1]
count = int(sys.argv[2])
dsts = int(count)
waypointclasses = int(sys.argv[3])
gplfile = open(sys.argv[4], 'w')

topology = Topology()
gplparser = GPLInterpreter(topoFile, topoFile, None, topology)
gplparser.parseTopo()


swCount = topology.getSwitchCount()
edgeSwitches = (topology.getSwitchCount() * 2/ 5) - 1  
k = int(math.sqrt(topology.getSwitchCount() * 4/ 5))

wclasses = []
for i in range(waypointclasses) : 
	while True : 
		wclass = []
		for j in range(2) : 
			w = random.randint(0,edgeSwitches)
			if w not in wclass : 
				wclass.append(w)
		
		w = random.randint(edgeSwitches + 1, swCount - 1)
		if w not in wclass : 
			wclass.append(w)
			
		wclass = sorted(wclass)
		if wclass not in wclasses :
			wclasses.append(wclass)
			break

waypointFile = open("waypoint-classes", 'w')
for i in range(len(wclasses)) :
	wclass = wclasses[i]
	wclassStr = ""
	for j in range(len(wclass)) :
		w = wclass[j]
		if w >= 2 * edgeSwitches + 2 : 
			waypoint = topology.getSwID("c" + str(w))
		elif w <= edgeSwitches : 
			waypoint = topology.getSwID("e" + str(w))
		else : 
			waypoint = topology.getSwID("a" + str(w))
		wclassStr += str(waypoint) + "-" 
	
	wclassStr = wclassStr[:len(wclassStr)-1]
	waypointFile.write(wclassStr)
	waypointFile.write("\n")

endpoints = []
for i in range(dsts) :
	while True:		
		d = random.randint(0,swCount - 1)
		wclass = wclasses[i % len(wclasses)]
		w1 = wclass[random.randint(0, len(wclass) - 1)]
		w2 = wclass[random.randint(0, len(wclass) - 1)]
		s1 = random.randint(0,swCount -1 )
		if s1 != d and s1 not in wclass and d not in wclass and w1 != w2 : 
			break
	
	if s1 >= 2 * edgeSwitches + 2 : 
		s1 = "c" + str(s1)
	elif s1 <= edgeSwitches :
		s1 = "e" + str(s1)
	else : 
		s1 = "a" + str(s1) 

	if d >= 2 * edgeSwitches + 2 : 
		d = "c" + str(d)
	elif d <= edgeSwitches :
		d = "e" + str(d)
	else : 
		d = "a" + str(d) 

	if w1 >= 2 * edgeSwitches + 2 : 
		w1 = "c" + str(w1)
	elif w1 <= edgeSwitches :
		w1 = "e" + str(w1)
	else : 
		w1 = "a" + str(w1) 

	if w2 >= 2 * edgeSwitches + 2 : 
		w2 = "c" + str(w2)
	elif w2 <= edgeSwitches :
		w2 = "e" + str(w2)
	else : 
		w2 = "a" + str(w2) 
	
	gplfile.write("p" + str(i) + "_" + str(0) + " := " + str(i) + " : " + s1  + " >> [ " + w1 + " ] >> " + str(d) + "\n")
	#gplfile.write("p" + str(i) + "_" + str(1) + " := " + str(i) + " : e" + str(s2)  + " >> [ " + w2 + " ] >> e" + str(d) + "\n")
	gplfile.write("p" + str(i) + "_" + str(1) + " := " + str(i) + " : " + s1  + " >> [ " + w2 + " ] >> " + str(d) + "\n")
	gplfile.write("p" + str(i) + "_" + str(2) + " := " + str(i) + " : " + str(s1)  + " >> [ " + w1 + " ] >> " + str(d) + "\n")
	#gplfile.write("p" + str(i) + "__" + str(1) + " := " + str(i) + " : e" + str(s2)  + " >> [ " + w1 + " ] >> e" + str(d) + "\n")

gplfile.write("== \n")	
for i in range(dsts) :
	gplfile.write("|| [ p" + str(i) + "_" + str(0) + ", p" +  str(i) + "_" + str(1) + " ]\n")
	#gplfile.write("|| [ p" + str(i) + "_" + str(1) + ", p" +  str(i) + "__" + str(1) + " ]\n")