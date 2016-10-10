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

if count == 1 : # If no of packet classes = group size, then there are no isolation policies
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



# for i in range(count) : 
# 	while True:
# 		s = random.randint(0,edgeSwitches)
# 		d = random.randint(0,edgeSwitches)
# 		if s <> d :
# 			break

	
# 	while True:
# 		a1 = random.randint(18,35)
# 		a2 = random.randint(18,35)
# 		a3 = random.randint(18,35)
# 		a4 = random.randint(18,35)
# 		if a1 <> a2 and a1 <> a3 and a2 <> a3: 
# 			if a1 <> a4 and a2 <> a4 and a3 <> a4 :
# 				break

	# if random.randint(0,5) == 2 : 
	# 	waypoint = s + d / 2
	# 	gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : " + topology.getSwName(s) + " >> [" + topology.getSwName(waypoint) + "] >> "  + topology.getSwName(d) + "\n")
	# else :
	#Reach	
	#gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> e" + str(d) + "\n")
	#Waypoint
	#gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : e" + str(s)  + " >> [ a" + str(a1) + ", a" + str(a2) + ", a" + str(a3) +  ", a" + str(a4) + " ] >> e" + str(d) + "\n")


# gplfile.write("== \n")

# isolatedPoliciesCount = count * (count - 1) * isolatePercentage / 200
# isolatedPolicies = []
# print "Number of isolation policies : ", isolatedPoliciesCount
# while isolatedPoliciesCount > 0 : 
# 	pc1 = random.randint(0,count - 1)
# 	pc2 = random.randint(0,count - 1)
# 	if pc1 > pc2 : 
# 		pc1,pc2 = pc2,pc1
# 	policy = [pc1,pc2]
# 	if pc1 == pc2 : 
# 		continue
# 	elif policy in isolatedPolicies : 
# 		continue
# 	else : 
# 		# Add isolation policy.
# 		isolatedPolicies.append(policy)
# 		isolatedPoliciesCount -= 1
# 		gplfile.write("p" + str(policy[0]) + " || " + "p" + str(policy[1]) + "\n")


# for i in range(count) : 
# 	s = random.randint(1,swCount/2)
# 	d = random.randint(swCount/2 + 1, swCount)
# 	if random.randint(0,5) == 2 : 
# 		waypoint = s + d / 2
# 		gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : " + topology.getSwName(s) + " >> [" + topology.getSwName(waypoint) + "] >> "  + topology.getSwName(d) + "\n")
# 	else :
# 		gplfile.write("p" + str(i) + " := tcp.port = " + str(i) + " : " + topology.getSwName(s) + " >> " + topology.getSwName(d) + "\n")

# gplfile.write("== \n")

# isolatedPoliciesCount = count * (count - 1) * isolatePercentage / 200
# isolatedPolicies = []
# print "Number of isolation policies : ", isolatedPoliciesCount
# while isolatedPoliciesCount > 0 : 
# 	pc1 = random.randint(0,count - 1)
# 	pc2 = random.randint(0,count - 1)
# 	if pc1 > pc2 : 
# 		pc1,pc2 = pc2,pc1
# 	policy = [pc1,pc2]
# 	if pc1 == pc2 : 
# 		continue
# 	elif policy in isolatedPolicies : 
# 		continue
# 	else : 
# 		# Add isolation policy.
# 		isolatedPolicies.append(policy)
# 		isolatedPoliciesCount -= 1
# 		gplfile.write("p" + str(policy[0]) + " || " + "p" + str(policy[1]) + "\n")



