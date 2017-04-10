#!/usr/bin/env python
import sys
import subprocess
import os
import random

if __name__ == "__main__":
	waypointGroups = [5]
	gpl_sizes = [10] #range(10,90,10)
	topofile = "./topologies/fattree-6.topo"
	useTactic = False
	tactic = "noEdgeLen7" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	for pcs in gpl_sizes : 
		for group in waypointGroups :
			for i in range(100) : 
				subprocess.call(["python", "GPLGenerator10.py", topofile, str(pcs), str(group), "1.gpl"])
				for i in range(10) : 
					workloadArgs = ["python", "-O", "genesis.py", "-c3", "-ospf", "-topo", topofile, "-gpl", "1.gpl"]
					if useTactic :
						workloadArgs.append("-useTactic")
						workloadArgs.append(tactic)
					if useDCSynthesis : 
						workloadArgs.append("-dc")
					
					subprocess.call(workloadArgs)
				#subprocess.call(["cat", "genesis-paths.txt"])
	
