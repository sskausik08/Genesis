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
dsts = isolatePercentage/2


endpoints = dict()
currdst = 0
for i in range(groups) :	
	srcGroup = dict()
	dstGroup = dict()
	for j in range(edgeSwitches + 1) :
		srcGroup[j] = 0
		dstGroup[j] = 0
	for dst in range(dsts) :
		while True:		
			d = random.randint(0,edgeSwitches)
			if dstGroup[d] < k/2 - 1:
				s1 = random.randint(0,edgeSwitches)
				s2 = random.randint(0,edgeSwitches)
				if s1 != d and s2 != d and s1 != s2 : 
					if srcGroup[s1] < k/2 - 1 and srcGroup[s2] < k/2 - 1:
						srcGroup[s1] += 1
						srcGroup[s2] += 1
						dstGroup[d] += 1
						break

		gplfile.write("p" + str(i) + "_" + str(dst) + " := " + str(currdst) + " : e" + str(s1)  + " >> e" + str(d) + "\n")
		gplfile.write("p" + str(i) + "__" + str(dst) + " := " + str(currdst) + " : e" + str(s2)  + " >> e" + str(d) + "\n")
		currdst += 1

if count == 1 : # If no of packet classes = group size, then there are no isolation policies
	exit(0)
gplfile.write("== \n")	
for i in range(groups) :
	sets = dict()
	for dst in range(dsts) : 
		setStr = "[ "
		setStr += "p" + str(i) + "_" + str(dst) + ", "
		setStr += "p" + str(i) + "__" + str(dst) + " ]"
		sets[dst] = setStr

	for dst1 in range(dsts) :
		for dst2 in range(dst1) :
			gplfile.write(sets[dst2] + " || " + sets[dst1] + "\n")



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



