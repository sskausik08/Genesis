#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	group_sizes = [2,5,10]
	gpl_sizes = [20, 40, 60]
	topofile = "./topologies/fattree-8.topo"
	useTactic = True
	tactic = "noEdge" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	for pcs in gpl_sizes : 
		for group in group_sizes :
			print " "
			print "Benchmark: " + str(pcs) + " packet classes, " + str(group) + " group size"
			subprocess.call(["python", "GPLGenerator.py", topofile, str(pcs), str(group), "1.gpl"])
			workloadArgs = ["python", "-O", "genesis.py", "-os", "-topo", topofile, "-gpl", "1.gpl"]
			if useTactic :
				workloadArgs.append("-useTactic")
				workloadArgs.append(tactic)
			if useDCSynthesis : 
				workloadArgs.append("-dc")
			
			subprocess.call(workloadArgs)
	