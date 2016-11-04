#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	zpl_sizes = range(100, 600, 100)
	topofile = "./topologies/40.topo"
	timeout = 600

	for pcs in zpl_sizes :
		print "Benchmark: " + str(pcs)
		for i in range(20) :
			workloadArgs = ["python", "-O", "zeppelin.py", "-topo", topofile, "-pc", str(pcs), "-ospf", "-subnets", str(int(pcs/4)), "-dist", str(5)]
			subprocess.call(workloadArgs)
