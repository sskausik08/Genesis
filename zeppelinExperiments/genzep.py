#!/usr/bin/env python
import sys
import subprocess
import os
import random

if __name__ == "__main__":
	group_sizes = [10]
	gpl_sizes = range(50,100,10)
	topofile = "./topologies/fattree-10.topo"
	useTactic = True
	tactic = "noEdgeLen7" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	for pcs in gpl_sizes : 
		for group in group_sizes :
			subprocess.call(["python", "GPLGenerator.py", topofile, str(pcs), str(group), "1.gpl"])
			for i in range(10) : 
				zepFile = open("zeppelin-timing", 'a')
				zepFile.write("Benchmark\t" + str(pcs) + "\t" + str(group) + "\n")
				zepFile.close()

				gplFile = open("1.gpl")
				outFile = open("2.gpl", 'w')

				lines = gplFile.readlines()
				pcR = range(pcs)
				random.shuffle(pcR)
				for l in pcR : 
					outFile.write(lines[l]) 
					outFile.write("\n")

				for l in range(pcs, len(lines)) : 
					outFile.write(lines[l]) 
					outFile.write("\n")

				workloadArgs = ["python", "-O", "genesis.py", "-c3", "-topo", topofile, "-gpl", "2.gpl"]
				if useTactic :
					workloadArgs.append("-useTactic")
					workloadArgs.append(tactic)
				if useDCSynthesis : 
					workloadArgs.append("-dc")
				
				subprocess.call(workloadArgs)
	