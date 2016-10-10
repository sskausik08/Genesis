#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	topofile = "./topologies/fattree-8.topo"

	# TE minimize average link utilization
	gpl_sizes = [100, 200]
	for pcs in gpl_sizes : 
		print " "
		print "Benchmark: " + str(pcs) + " packet classes, minimize average link utilization" 
		subprocess.call(["python", "GPLGenerator3.py", topofile, str(pcs), "minimize-avg-te", "1.gpl"]) 
		workloadArgs = ["python", "-O", "genesis.py", "-topo", topofile, "-gpl", "1.gpl"]
		subprocess.call(workloadArgs)

	# TE minimize max link utilization
	gpl_sizes = [25, 50]
	for pcs in gpl_sizes : 
		print " "
		print "Benchmark: " + str(pcs) + " packet classes, minimize max link utilization" 
		subprocess.call(["python", "GPLGenerator3.py", topofile, str(pcs), "minimize-max-te", "1.gpl"]) 
		workloadArgs = ["python", "-O", "genesis.py", "-topo", topofile, "-gpl", "1.gpl"]
		subprocess.call(workloadArgs)

	# Network repair experiment
	for i in range(10) : 
		pcs = 80
		groupsize = 10
		# Network repair workload
		print " "
		print "Benchmark: " + str(pcs) + " packet classes, " + str(groupsize) + "group size, tenant-isolation, 1-switch failure"
		subprocess.call(["python", "GPLGenerator.py", topofile, str(pcs), str(groupsize), "1.gpl"]) 
		workloadArgs = ["python", "-O", "genesis.py", "-topo", topofile, "-gpl", "1.gpl", "-repair"]
		subprocess.call(workloadArgs)
	