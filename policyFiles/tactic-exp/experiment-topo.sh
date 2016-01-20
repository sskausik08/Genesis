touch constraints_eval
python GPLGenerator.py ./topologies/fattree-6.topo 1 1 ./policyFiles/tactic-exp/1.gpl
python -O genesis.py -topo ./topologies/fattree-6.topo -gpl ./policyFiles/tactic-exp/1.gpl >> constraints_eval
python GPLGenerator.py ./topologies/fattree-8.topo 1 1 ./policyFiles/tactic-exp/1.gpl
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/tactic-exp/1.gpl >> constraints_eval
python GPLGenerator.py ./topologies/fattree-10.topo 1 1 ./policyFiles/tactic-exp/1.gpl
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/tactic-exp/1.gpl >> constraints_eval
python GPLGenerator.py ./topologies/fattree-12.topo 1 1 ./policyFiles/tactic-exp/1.gpl
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/tactic-exp/1.gpl >> constraints_eval


