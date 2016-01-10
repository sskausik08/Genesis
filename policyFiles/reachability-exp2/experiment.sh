touch reachability_timing
python GPLGenerator.py ./topologies/fattree-8.topo 100 1 ./policyFiles/reachability-exp2/fat8-100.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 200 1 ./policyFiles/reachability-exp2/fat8-200.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 300 1 ./policyFiles/reachability-exp2/fat8-300.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 400 1 ./policyFiles/reachability-exp2/fat8-400.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 500 1 ./policyFiles/reachability-exp2/fat8-500.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 600 1 ./policyFiles/reachability-exp2/fat8-600.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 700 1 ./policyFiles/reachability-exp2/fat8-700.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 800 1 ./policyFiles/reachability-exp2/fat8-800.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 900 1 ./policyFiles/reachability-exp2/fat8-900.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 1000 1 ./policyFiles/reachability-exp2/fat8-1000.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 1500 1 ./policyFiles/reachability-exp2/fat8-1500.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 2000 1 ./policyFiles/reachability-exp2/fat8-2000.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 2500 1 ./policyFiles/reachability-exp2/fat8-2500.gpl
python GPLGenerator.py ./topologies/fattree-8.topo 3000 1 ./policyFiles/reachability-exp2/fat8-3000.gpl
echo "8 topo" >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-100.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-200.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-300.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-400.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-600.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-700.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-800.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-900.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-1000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-1500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-2000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-2500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-8.topo -gpl ./policyFiles/reachability-exp/fat8-3000.gpl -useTactic >> reachability_timing
python GPLGenerator.py ./topologies/fattree-10.topo 100 1 ./policyFiles/reachability-exp2/fat8-100.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 200 1 ./policyFiles/reachability-exp2/fat8-200.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 300 1 ./policyFiles/reachability-exp2/fat8-300.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 400 1 ./policyFiles/reachability-exp2/fat8-400.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 500 1 ./policyFiles/reachability-exp2/fat8-500.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 600 1 ./policyFiles/reachability-exp2/fat8-600.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 700 1 ./policyFiles/reachability-exp2/fat8-700.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 800 1 ./policyFiles/reachability-exp2/fat8-800.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 900 1 ./policyFiles/reachability-exp2/fat8-900.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 1000 1 ./policyFiles/reachability-exp2/fat8-1000.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 1500 1 ./policyFiles/reachability-exp2/fat8-1500.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 2000 1 ./policyFiles/reachability-exp2/fat8-2000.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 2500 1 ./policyFiles/reachability-exp2/fat8-2500.gpl
python GPLGenerator.py ./topologies/fattree-10.topo 3000 1 ./policyFiles/reachability-exp2/fat8-3000.gpl
echo "10 topo" >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-100.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-200.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-300.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-400.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-600.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-700.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-800.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-900.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-1000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-1500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-2000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-2500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-10.topo -gpl ./policyFiles/reachability-exp/fat8-3000.gpl -useTactic >> reachability_timing
python GPLGenerator.py ./topologies/fattree-12.topo 100 1 ./policyFiles/reachability-exp2/fat8-100.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 200 1 ./policyFiles/reachability-exp2/fat8-200.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 300 1 ./policyFiles/reachability-exp2/fat8-300.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 400 1 ./policyFiles/reachability-exp2/fat8-400.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 500 1 ./policyFiles/reachability-exp2/fat8-500.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 600 1 ./policyFiles/reachability-exp2/fat8-600.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 700 1 ./policyFiles/reachability-exp2/fat8-700.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 800 1 ./policyFiles/reachability-exp2/fat8-800.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 900 1 ./policyFiles/reachability-exp2/fat8-900.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 1000 1 ./policyFiles/reachability-exp2/fat8-1000.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 1500 1 ./policyFiles/reachability-exp2/fat8-1500.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 2000 1 ./policyFiles/reachability-exp2/fat8-2000.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 2500 1 ./policyFiles/reachability-exp2/fat8-2500.gpl
python GPLGenerator.py ./topologies/fattree-12.topo 3000 1 ./policyFiles/reachability-exp2/fat8-3000.gpl
echo "12 topo" >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-100.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-200.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-300.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-400.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-600.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-700.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-800.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-900.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-1000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-1500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-2000.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-2500.gpl -useTactic >> reachability_timing
python -O genesis.py -topo ./topologies/fattree-12.topo -gpl ./policyFiles/reachability-exp/fat8-3000.gpl -useTactic >> reachability_timing