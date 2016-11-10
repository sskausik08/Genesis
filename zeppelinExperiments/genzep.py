#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	group_sizes = [2,5,10]
	gpl_sizes = range(10,90,10)
	topofile = "./topologies/fattree-8.topo"
	useTactic = True
	tactic = "noEdgeLen7" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	for i in range(20) : 
		for pcs in gpl_sizes : 
			for group in group_sizes :
				zepFile = open("zeppelin-timing", 'a')
				zepFile.write("Benchmark\t" + str(pcs) + "\t" + str(group) + "\n")
				zepFile.close()
				subprocess.call(["python", "GPLGenerator.py", topofile, str(pcs), str(group), "1.gpl"])
				workloadArgs = ["python", "-O", "genesis.py", "-c3", "-topo", topofile, "-gpl", "1.gpl"]
				if useTactic :
					workloadArgs.append("-useTactic")
					workloadArgs.append(tactic)
				if useDCSynthesis : 
					workloadArgs.append("-dc")
				
				subprocess.call(workloadArgs)
	