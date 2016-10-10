POPL Artifact Evaluation Readme
======================================
#35   Genesis: Data Plane Synthesis in Multi-Tenant Networks

======================================
Running Genesis:
The Virtual Machine (Ubuntu 14.04) comes with all packages installed. 
To run Genesis, go to the ~/Genesis folder and use the terminal to run Genesis:

	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename>

To run Genesis with tactic enabled:
	
	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename> -useTactic <tactic>

Our current implementation supports 4 tactics that can be supplied as arguments 
(implemented in useTactic() method in GenesisSynthesiser.py):
	"noEdge" : the edge-to-edge path will not contain another edge switch in the path
	"valleyFree" : valley-free routing, that is paths are of the form eacae
	"len7" : Length of path <= 7
	"noEdgeLen7" : Length of path <= 7 and does not contain another path.

[Note: these tactics assume that each paths start and end at edge switches. New tactics
can be added to generalize these tactics]

To run Genesis using divide-and-conquer synthesis: 

	python -O genesis.py -topo <topology-filename> -gpl <gpl-filename> -dc

To run Genesis for <b>network repair</b>:
	
	python -O genesis.py -topo [topology-filename] -gpl [gpl-filename] -repair

======================================
GPL syntax: 
To define a packet class(pc) -
		p0_0 := tcp.port = 0 : e14 >> e17

<pc-name>  <network-predicate> <source-sw> >> <destination-sw>
The current implementation of Genesis simply uses the network predicate as 
a string. For actual network deployments, the network predicate would 
translate to SDN Match rules.

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

======================================
Output of Genesis:
Genesis in its current form gives the paths for each packet class 
(written to genesis-paths.txt) which satisfy the input policies. From these paths,
rules for a software-defined network can be trivially constructed (written 
to .genesis-forwarding-rules). 
If unsatisfiable, it returns that "Input policies not reasible" and exits. 

Validation: In PolicyDatabase.py, the output paths of Genesis
is validated with respect to the input policies to detect violations
to the policies. This helps us verify the correctness of Genesis's output. 

======================================
Topology Files:
The fat-tree topology files with varying number of switches can be found
in topologies folder: 
fattree-6.topo: 45 switches 
fattree-8.topo: 80 switches 

======================================
Evaluation on Benchmarks:
We provide scripts pertaining to the experiments ran in the paper. We 
present the synthesis time taken by the Z3 solver i.e., time taken 
for Z3 for the check() method. We ignore the total time taken by 
Genesis (parsing, generating constraints etc.), instead the major bottleneck
is the solve time (high complexity), thus, we report in the paper 
the time taken to solve the constraints. The experiments were conducted 
on a 32-core Intel-Xeon 2.40GHz CPU machine and 128GB of RAM, thus a virtual machine
may report higher synthesis times. 

================
Multi-tenant Isolation Workloads - AEC/isolation.py
Execute the isolation.py (no command-line arguments) from the Genesis directory 
(it uses genesis.py and GPLGenerator.py, a python program which generates GPL files
based on different parameter values). Refer to Sec8.1 in paper. 

The isolation.py file can be modified to run different multi-tenant isolation workloads. 
The different parameters are: 
Number of packet classes = [20,40,60]
Group size = [2,5,10]
useTactic = True/False 
tactic = The tactic to apply (one of noEdge, valleyFree, len7, noEdgeLen7)
useDCSynthesis = True/False 

================
Isolation Workloads for varying topology sizes - AEC/linkcapacity.py
Execute the linkcapacity.py (no command-line arguments) from the Genesis directory
with linkcapacity parameter in the script set to False. This script can be 
used to run the tactic reduction experiments by running 
the script (linkcapacity=False) with different tactics.

================
Link Capacity Experiment - AEC/linkcapacity.py
Execute the linkcapacity.py (no command-line arguments) from the Genesis directory
with linkcapacity parameter in the script set to True.
This uses GPLGenerator5.py which generates a isolation workload with 10 additional
link capacity policies. This script can use to run the link capacity with
tactics as well [useTactic = True, tactic = noEdge/...]

================
Waypoint Experiment - AEC/waypoint.py
Execute the waypoint.py (no command-line arguments) from the Genesis directory.

NOTE: One change from other experiments is that max path length has to be SET to 15 before
running these experiments.
This is set in the Topology class (in Topology.py) variable 
			self.maxPathLength = 15

This experiment uses GPLGenerator6.py to generate the waypoint GPL files as
described in the paper. 

================
Optimization Experiments - AEC/optimization.py
Execute the optimization.py (no command-line arguments) from the Genesis directory.
It contains three different experiments: measuring performance of TE 
objectives: minimizing average link utilization and minimizing max link utilization,
and a network repair experiment. 

This experiment uses GPLGenerator3.py for generating the TE workloads.

======================================
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

========================================

Installing Genesis on Ubuntu 14.04

Genesis comes with a install script intended to install 
all dependencies of Genesis. The install script can be found
in the Genesis directory - install 

Copy install to $HOME, and from $HOME, run on terminal:
	
	chmod +x install
	sudo ./install

Open a new terminal to run Genesis (.bash_profile updated by install)