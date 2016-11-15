from Topology import Topology
from GPLInterpreter import GPLInterpreter
import sys
import random
import math

if len(sys.argv) <> 5 : 
	print "python GPLGenerator6.py <topology-file> <number-of-packet-classes> <number-of-waypoints> <gpl-filename>"
	exit(0)
topoFile = sys.argv[1]
count = int(sys.argv[2])
waypoints = int(sys.argv[3])
gplfile = open(sys.argv[4], 'w')

topology = Topology()
gplparser = GPLInterpreter(topoFile, topoFile, None, topology)
gplparser.parseTopo()


swCount = topology.getSwitchCount()
edgeSwitches = (topology.getSwitchCount() * 2/ 5) - 1  
k = int(math.sqrt(topology.getSwitchCount() * 4/ 5))

endpoints = []

for i in range(count) : 
	while True:
		s = random.randint(0,edgeSwitches)
		d = random.randint(0,edgeSwitches)
		if s <> d and [s,d] not in endpoints:
			endpoints.append([s,d])
			break

	
	while True:
		a1 = random.randint(edgeSwitches + 1, 2 * edgeSwitches - 3)
		a2 = random.randint(2 * edgeSwitches + 2, swCount - 1)
		a3 = random.randint(edgeSwitches + 1, 2 * edgeSwitches - 3)
		a4 = random.randint(2 * edgeSwitches + 2, swCount - 1)
		a5 = random.randint(edgeSwitches + 1, 2 * edgeSwitches - 3)
		if a1 <> a2 and a1 <> a3 and a1 <> a4 and a1 <> a5: 
			if a2 <> a3 and a2 <> a4 and a2 <> a5 :
				if a3 <> a4  and a3 <> a5 and a4 <> a5 : 
					break
	if waypoints == 5: 
		val = random.randint(0,5) 
		if val == 0 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + ", a" + str(a3) +  ", c" + str(a4) + ", a" + str(a5) + " ] >> e" + str(d) + "\n")
		elif val == 1 :
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "; a" + str(a3) +  "; c" + str(a4) + "; a" + str(a5) + " ] >> e" + str(d) + "\n")
		elif val == 2 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + "; a" + str(a3) +  ", c" + str(a4) + ", a" + str(a5) + " ] >> e" + str(d) + "\n")
		elif val == 3 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + " , a" + str(a3) +  "; c" + str(a4) + ", a" + str(a5) + " ] >> e" + str(d) + "\n")
		elif val == 4 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "; a" + str(a3) +  ", c" + str(a4) + ", a" + str(a5) + " ] >> e" + str(d) + "\n")
		elif val == 5 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + ", a" + str(a3) +  "; c" + str(a4) + "; a" + str(a5) + " ] >> e" + str(d) + "\n")
	elif waypoints == 4 : 
		val = random.randint(0,5) 
		if val == 0 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + ", a" + str(a3) +  ", c" + str(a4) +  "] >> e" + str(d) + "\n")
		elif val == 1 :
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "; a" + str(a3) +  "; c" + str(a4) +  "] >> e" + str(d) + "\n")
		elif val == 2 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + "; a" + str(a3) +  ", c" + str(a4) +  "] >> e" + str(d) + "\n")
		elif val == 3 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + " , a" + str(a3) +  "; c" + str(a4) +  "] >> e" + str(d) + "\n")
		elif val == 4 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "; a" + str(a3) +  ", c" + str(a4) +  "] >> e" + str(d) + "\n")
		elif val == 5 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + ", a" + str(a3) +  "; c" + str(a4) +  "] >> e" + str(d) + "\n")
	elif waypoints == 3:
		val = random.randint(0,3) 
		if val == 0 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + ", a" + str(a3) +   "] >> e" + str(d) + "\n")
		elif val == 1 :
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "; a" + str(a3) +   "] >> e" + str(d) + "\n")
		elif val == 2 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + "; a" + str(a3) +   "] >> e" + str(d) + "\n")
		elif val == 3 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + " , a" + str(a3) +   "] >> e" + str(d) + "\n")
	elif waypoints == 2:
		val = random.randint(0,1) 
		if val == 0 : 
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", c" + str(a2) + "] >> e" + str(d) + "\n")
		elif val == 1 :
			gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "; c" + str(a2) + "] >> e" + str(d) + "\n")
	else : 
		gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + "] >> e" + str(d) + "\n")




