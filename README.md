
Genesis: Data Plane Synthesis in Multi-tenant Networks
====================
Authors:
- Kausik Subramanian 
- Loris D'Antoni
- Aditya Akella

To appear in Proc. of the ACM Symposium on Principles of Programming Languages (POPL), 2017

Abstract: 
Operators in multi-tenant cloud datacenters re- quire support for diverse and complex end-to-end policies, such as, reachability, middlebox traversals, isolation, traffic engineering, and network resource management. We present Genesis, a data-center network management system which allows policies to be specified in a declarative manner without explicitly programming the network data plane. Genesis tackles the problem of enforcing policies by synthesizing switch forwarding tables. It uses the formal foundations of constraint solving in combination with fast off-the-shelf SMT solvers. To improve synthesis performance, Genesis incorporates a novel search strategy that uses regular expressions to specify properties that leverage the structure of datacenter networks, and a divide-and-conquer synthesis procedure which exploits the structure of policy relationships. We have prototyped Genesis, and conducted experiments with a variety of workloads on real-world topologies to demonstrate its performance.
