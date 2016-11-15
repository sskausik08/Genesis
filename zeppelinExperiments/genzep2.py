#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	pcs = 100
	topofile = "./topologies/fattree-8.topo"

	for w in range(4) : 
			print " "
			print "Benchmark: " + str(pcs) + " packet classes, " + str(w) + " waypoints"
			subprocess.call(["python", "GPLGenerator6.py", topofile, str(pcs), str(w), "1.gpl"])
			for i in range(10) : 
				zepFile = open("zeppelin-timing", 'a')
				zepFile.write("Benchmark\t" + str(pcs) + "\t" + str(w) + "\n")
				subprocess.call(["shuf", "1.gpl", "-o", "2.gpl"])
				workloadArgs = ["python", "-O", "genesis.py", "-c3", "-topo", topofile, "-gpl", "1.gpl"]
				subprocess.call(workloadArgs)