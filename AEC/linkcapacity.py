#!/usr/bin/env python
import sys
import subprocess
import os

if __name__ == "__main__":
	group_sizes = 5
	workloads = [["fattree-6.topo", 15], ["fattree-8.topo", 30], ["fattree-10.topo",60], ["fattree-12.topo", 100]]
	groupsize = 5
	linkCapacity = True
	useTactic = True
	tactic = "noEdge"

	for w in workloads : 
			print " "
			print "Benchmark: Topology: " + w[0] + " packet classes " + str(w[1])

			if linkCapacity : 
				# Generate gpl isolation workload with link capacities
				subprocess.call(["python", "GPLGenerator5.py", "./topologies/" + w[0], str(w[1]), str(groupsize), "1.gpl"])
			else : 
				# Generate gpl workload without link capacities
				subprocess.call(["python", "GPLGenerator.py", "./topologies/" + w[0], str(w[1]), str(groupsize), "1.gpl"])
			
			# Workload Args to Genesis
			workloadArgs = ["python", "-O", "genesis.py", "-topo", "./topologies/" + w[0], "-gpl", "1.gpl"]
			if useTactic :
				workloadArgs.append("-useTactic")
				workloadArgs.append(tactic)
			
			subprocess.call(workloadArgs)
	