
Genesis : Flow Table Synthesis
====================
Authors:
- Kausik Subramanian 
- Loris D'Antoni
- Aditya Akella


Input
-----
-   Network topology graph (comprising of hosts, switches, links)

-   End-point (for a pair of end-points) based network-wide policies.
    For eg.

    -   ALLOW flows : $\exists Path(h1,h2)$ (Furthermore we can try to
        reason about shortest path)

    -   DENY flows : $\neg (\exists Path(h2,h3))$

    -   No infinite loops in the graph for a flow :
        $\forall s. \neg (\exists Path(s,s))$ (This is implicitly
        inferred if we can guarantee reachability. However, we can have
        valid finite loops in the graph (service chaining for example).
        We don’t need to check for loops in the graph now. )

    -   Traffic isolation : Flows f1, f2 should not share a link in the
        path :
        $\neg (\exists l. l \in Links(f1) \wedge l \in Links(f2))$

    -   Flows pass through a waypoint (e.g Middlebox, firewall etc.) A
        extension of this is middlebox service chaining $\rightarrow$
        flow has to pass through a sequence of nodes.

    -   Support for multi-path for a single flow, where the multiple
        paths are isolated (no common links). For example, the policy
        can be that for Flow $f$, $f.tag = 1$ and $.f.tag =2$ traverse
        different paths in the network.

Output
------

The flow tables in the switches satisfying input policies.

