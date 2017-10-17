#!/usr/bin/env python
import sys
import subprocess
import os
import random

if __name__ == "__main__":
	gpl_sizes = range(10, 210,10)
	topofile = "./topologies/fattree-6.topo"
	useTactic = False
	tactic = "noEdgeLen7" # Tactics: noEdge, valleyFree, len7, noEdgeLen7
	useDCSynthesis = False

	
	f = open('zeppelin-timing', 'a')
	f.write("Reachability\n")
	f.close()
	for pcs in gpl_sizes : 
		for i in range(10) : # "-c3", "-ospf", 
			subprocess.call(["python", "GPLGenerator11.py", topofile, str(pcs), str(pcs), "1.gpl"])
			workloadArgs = ["python", "-O", "genesis.py", "-c3", "-ospf", "-topo", topofile, "-gpl", "1.gpl"]
			if useTactic :
				workloadArgs.append("-useTactic")
				workloadArgs.append(tactic)
			if useDCSynthesis : 
				workloadArgs.append("-dc")
			
			subprocess.call(workloadArgs)
				#subprocess.call(["cat", "genesis-paths.txt"])
	
