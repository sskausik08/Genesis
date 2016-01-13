touch linkcap1_timing
python GPLGenerator2.py ./topologies/geant.topo 50 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap1_timing
python GPLGenerator2.py ./topologies/geant.topo 100 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap1_timing
python GPLGenerator2.py ./topologies/geant.topo 150 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap1_timing
python GPLGenerator2.py ./topologies/geant.topo 200 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap1_timing
python GPLGenerator2.py ./topologies/geant.topo 250 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap1_timing
