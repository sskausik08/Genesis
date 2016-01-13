touch linkcap2_timing
python GPLGenerator2.py ./topologies/geant.topo 100 10 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap2_timing
python GPLGenerator2.py ./topologies/geant.topo 100 20 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap2_timing
python GPLGenerator2.py ./topologies/geant.topo 100 30 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap2_timing
python GPLGenerator2.py ./topologies/geant.topo 100 40 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap2_timing
python GPLGenerator2.py ./topologies/geant.topo 100 50 ./policyFiles/linkcap-exp/1.gpl
python -O genesis.py -topo ./topologies/geant.topo -gpl ./policyFiles/linkcap-exp/1.gpl >> linkcap2_timing
