#!/usr/bin/env python
import sys
import subprocess
import os
import random

if __name__ == "__main__":
	waypointGroups = [2, 5, 10]
	gpl_sizes = range(10,110,10)
	topofile = "./topologies/fattree-6.topo"
	useTactic = False
	tactic = "noEdgeLen7" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	for pcs in gpl_sizes : 
		for group in waypointGroups :
			subprocess.call(["python", "GPLGenerator8.py", topofile, str(pcs), str(group), "1.gpl"])
			for i in range(10) : 
				workloadArgs = ["python", "-O", "genesis.py", "-c3", "-ospf", "-topo", topofile, "-gpl", "1.gpl"]
				if useTactic :
					workloadArgs.append("-useTactic")
					workloadArgs.append(tactic)
				if useDCSynthesis : 
					workloadArgs.append("-dc")
				
				subprocess.call(workloadArgs)
				#subprocess.call(["cat", "genesis-paths.txt"])
	
