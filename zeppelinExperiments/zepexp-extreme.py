#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	zpl_sizes = range(200, 1200, 200)
	topofile = "./topologies/125.topo"
	timeout = 600

	for pcs in zpl_sizes :
		print "Benchmark: " + str(pcs)
		for i in range(20) :
			workloadArgs = ["python", "-O", "zeppelin.py", "-topo", topofile, "-pc", str(pcs), "-to", str(timeout), "-subnets", str(int(pcs/4)), "-dist", str(10), "-domains", str(5), "-configOpt"]
			subprocess.call(workloadArgs)


	zpl_sizes = range(200, 1200, 200)
	topofile = "./topologies/125.topo"
	timeout = 600

	for pcs in zpl_sizes :
		print "Benchmark: " + str(pcs)
		for i in range(20) :
			workloadArgs = ["python", "-O", "zeppelin.py", "-topo", topofile, "-pc", str(pcs), "-to", str(timeout), "-subnets", str(int(pcs/4)), "-dist", str(10), "-domains", str(5), "-rfOpt"]
			subprocess.call(workloadArgs)