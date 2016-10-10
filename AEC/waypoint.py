#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	pcs = 100
	topofile = "./topologies/fattree-8.topo"

	for w in range(1, 6) : 
			print " "
			print "Benchmark: " + str(pcs) + " packet classes, " + str(w) + " waypoints"
			subprocess.call(["python", "GPLGenerator6.py", topofile, str(pcs), str(w), "1.gpl"])
			workloadArgs = ["python", "-O", "genesis.py", "-topo", topofile, "-gpl", "1.gpl"]
			subprocess.call(workloadArgs)