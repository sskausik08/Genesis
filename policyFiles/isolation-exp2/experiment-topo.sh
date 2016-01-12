touch isolation3_timing
python GPLGenerator.py ./topologies/fattree-6.topo 25 5 ./policyFiles/isolation-exp2/1.gpl
python -O genesis.py -topo ./topologies/fattree-6.topo -gpl ./policyFiles/isolation-exp2/1.gpl -useTactic >> isolation3_timing
python GPLGenerator.py ./topologies/fattree-8.topo 65 5 ./policyFiles/isolation-exp2/1.gpl
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/isolation-exp2/1.gpl -useTactic >> isolation3_timing
python GPLGenerator.py ./topologies/fattree-10.topo 125 5 ./policyFiles/isolation-exp2/1.gpl
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/isolation-exp2/1.gpl -useTactic >> isolation3_timing
python GPLGenerator.py ./topologies/fattree-12.topo 215 5 ./policyFiles/isolation-exp2/1.gpl
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/isolation-exp2/1.gpl -useTactic >> isolation3_timing


