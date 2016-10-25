#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	zpl_sizes = [1000]
	topofile = "./topologies/ion.topo"

	for pcs in zpl_sizes :
		print "Benchmark: " + str(pcs)
		for i in range(100) :
			workloadArgs = ["python", "-O", "zeppelin.py", "-topo", topofile, "-pc", str(pcs)]
			subprocess.call(workloadArgs)
