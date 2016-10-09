POPL Artifact Evaluation Readme
======================================
#35   Genesis: Data Plane Synthesis in Multi-Tenant Networks

Pointers to code corresponding to the different sections of the paper:
Section 2: Genesis Policy Language - GPLInterpreter.py

Section 3: Synthesis of Forwarding Rules - GenesisSynthesiser.py     
Input for synthesis:
1) Topology data - Topology.py
2) Policies - PolicyDatabase.py

Functions in GenesisSynthesiser.py for each type of policy:

Section 4.2: Reachability - addReachabilityConstraints(), addPathConstraints()

Section 4.3: Waypoints - addReachabilityConstraints(), addSinglePathConstraints()

Section 4.4: Isolation - addTrafficIsolationConstraints()

Section 5.1: Link/Switch Capacity - addLinkConstraints(), addSwitchTableConstraints()

Section 5.2: Traffic Engineering - addAverageUtilizationMinimizationConstraints(), addMaxUtilizationMinimizationConstraints()

Section 5.3.2: Network Repair - enforceChangedPolicies() 
[Emulates network repair when the switch with maximum number of rules fails]

Section 6: Tactics - Tactic.py

Section 7: Divide-and-Conquer Synthesis - enforceGraphPoliciesDC() in GenesisSynthesiser.py 
			Solution Recovery - differentSolutionRecovery()

Running Genesis:
The Virtual Machine (Ubuntu 14.04) comes with all packages installed. 
To run Genesis, go to the ~/Genesis folder and use the terminal to run Genesis:

	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename>

To run Genesis with tactic enabled (the tactic to use is set in useTactic() method 
in GenesisSynthesiser.py, we have provided the tactics mentioned in the paper):
	
	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename> -useTactic

To run Genesis using divide-and-conquer synthesis: 

	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename> -dc


GPL syntax: 
To define a packet class(pc) -
		p0_0 := tcp.port = 0 : e14 >> e17

<pc-name>  <network-predicate> <source-sw> >> <destination-sw>
The current implementation of Genesis simply uses the network predicate as 
a string, even deploying the rules to a actual software-defined network, we 
can 

To add waypoints to a reachability policy:
		e11 >> [ a29, a24; a20, a28 ] >> e2 
which enforces that [a29, a24] must be traversed before [a20, a28] in the path,
and ordering in a set is irrelevant.

To define an isolation policy using the packet class names-
		pc1 || pc2 
To define isolation among different sets of classes - 
	[pc1, pc2] || [pc3, pc4] 
=> pc1 || pc3 and pc1 || pc4 and pc2 || pc3 and pc2 || p4

To define a link capacity policy:
	e11 -> a28 : capacity-value

To define a switch table size policy:
	e11 : size

For traffic engineering, specify:
	minimize-avg-te
or 
	minimize-max-te 


Output of Genesis:
Genesis in its current form gives the paths for each packet class 
(written to genesis-paths.txt) which satisfy the input policies. From these paths,
rules for a software-defined network can be trivially constructed (written 
to .genesis-forwarding-rules). 
If unsatisfiable, it returns that "Input policies not reasible" and exits. 

Validation: In PolicyDatabase.py, the output paths of Genesis
is validated with respect to the input policies to detect violations
to the policies. This helps us verify the correctness of Genesis's output. 


Topology Files:
The fat-tree topology files with varying number of switches can be found
in topologies folder: 
fattree-6.topo: 45 switches 
fattree-8.topo: 80 switches 

Benchmarks:


Multi-tenant Isolation Workloads - AEC/isolation.py
Execute the isolation.py (no command-line arguments) from the Genesis directory 
(it uses genesis.py and GPLGenerator.py, a python program which generates GPL files
based on different parameter values). 
The isolation.py file can be modified to run different multi-tenant isolation workloads. 
Different parameters are [refer to Sec8.1 in paper : 
Number of packet classes = [20,40,60]
Group size = [2,5,10]
useTactic = True/False
useDCSynthesis = True






