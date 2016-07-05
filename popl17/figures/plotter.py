# Color Scheme
#e41a1c
#377eb8
#4daf4a
#984ea3
#ff7f00
#ffff33
#f781bf

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

x = [10,20,30,40,50,60,70,80]

noTacticFig = plt.figure(1)

noTactic1 = [0.18,0.8640999794,2.036143065,16.71143389,643,4005.580206,11894.67818,15000]
noTactic2 = [0.17,0.8066310883, 2.146327019, 21.74198389, 58,211.5037289, 7000, 10000]
noTactic5 = [0.14,0.6872601509,1.693818092,2.794470072,43.64237714,190.4395521,2558,5000]
noTactic10 = [0.13,0.4372241497,1.165225983,2.570262909,4.928798914,6.639307022,453,2353.869107]

markersize = 11

plt.plot(x, noTactic1, '#ff7f00', marker="o", markersize=markersize, label="Group Size:1")
plt.plot(x, noTactic2, '#377eb8', marker="^", markersize=markersize, label="Group Size:2")
plt.plot(x, noTactic5, '#4daf4a', marker="D", markersize=markersize, label="Group Size:5")
plt.plot(x, noTactic10, '#984ea3', marker="s", markersize=markersize, label="Group Size:10")


plt.yscale('log')
plt.ylim(ymax=5000)

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Packet Classes', fontsize=20)
plt.ylabel('Synthesis Time (log s)', fontsize=20)

plt.grid()
plt.savefig('noTacticIsolation.eps', format='eps', dpi=1000, bbox_inches='tight')

edgeTacticFig = plt.figure(2)
edgeTactic1 = [0.18,1.02,2.06,4.09,145,416,2784,7842]
edgeTactic2 = [0.16,0.79,1.86,3.7,74,301,1601,3413]
edgeTactic5 = [0.13,0.63,1.57,3.26,22.6,71,647,1506]
edgeTactic10 = [0.13,0.42,1.37,2.48,6.58,8.23,54,292]

# red dashes, blue squares and green triangles
plt.plot(x, edgeTactic1, '#ff7f00', marker="o", markersize=markersize, label="Group Size:1")
plt.plot(x, edgeTactic2, '#377eb8', marker="^", markersize=markersize, label="Group Size:2")
plt.plot(x, edgeTactic5, '#4daf4a', marker="D", markersize=markersize, label="Group Size:5")
plt.plot(x, edgeTactic10, '#984ea3', marker="s", markersize=markersize, label="Group Size:10")


plt.yscale('log')
plt.ylim(ymax=5000)

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Packet Classes', fontsize=20)
plt.ylabel('Synthesis Time (log s)', fontsize=20)

plt.grid()
plt.savefig('edgeTacticIsolation.eps', format='eps', dpi=1000,  bbox_inches='tight')

noValleyTacticFig = plt.figure(3)
noValleyTactic1 = [0.11,0.59,1.33,2.66,4.22,8.41,13.05,19.81]
noValleyTactic2 = [0.1,0.58,1.55,2.48,4,8.01,9.8,18.16]
noValleyTactic5 = [0.08,0.41,1.24,2.29,4.47,5.9,8.8,13.85]
noValleyTactic10 = [0.07,0.3,0.9,1.96,3.45,5.5,8.6,12.97]


# red dashes, blue squares and green triangles
plt.plot(x, noValleyTactic1, '#ff7f00', marker="o", markersize=markersize, label="Group Size:1")
plt.plot(x, noValleyTactic2, '#377eb8', marker="^", markersize=markersize, label="Group Size:2")
plt.plot(x, noValleyTactic5, '#4daf4a', marker="D", markersize=markersize, label="Group Size:5")
plt.plot(x, noValleyTactic10, '#984ea3', marker="s", markersize=markersize, label="Group Size:10")

plt.yscale('log')
plt.ylim(ymax=5000)

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Packet Classes', fontsize=20)
plt.ylabel('Synthesis Time (log s)', fontsize=20)

plt.grid()
plt.savefig('noValleyTacticIsolation.eps', format='eps', dpi=1000,  bbox_inches='tight')

# Topology
x = [45,80,125,180]

isolationTopologyFig = plt.figure(4)

noTactic = [0.0122,0.0804,2.0785,9.6241]
noEdge = [0.0086,0.05433333333,0.2631666667,2.58618]
len7 = [0.007133333333,0.043,0.2188333333,1.0793]
len7noEdge = [0.007133333333,0.044,0.2468333333,1.0075]
noValley = [0.004666666667,0.03766666667,0.2056666667,0.7277]

plt.plot(x, noTactic, '#ff7f00', marker="o", markersize=markersize, label="Baseline")
plt.plot(x, noEdge, '#e41a1c', marker="^", markersize=markersize, label="No Edge")
plt.plot(x, len7, '#4daf4a', marker="h", markersize=markersize, label="Len <= 7")
plt.plot(x, len7noEdge, '#984ea3', marker="s", markersize=markersize, label="No Edge and Len <= 7")
plt.plot(x, noValley, '#377eb8', marker="D", markersize=markersize, label="Valley-Free")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Switches', fontsize=20)
plt.ylabel('Avg. Synthesis Time per Class(s)', fontsize=20)

plt.grid()
plt.savefig('isolationTopology.eps', format='eps', dpi=1000,  bbox_inches='tight')

linkFig = plt.figure(5)

noTactic = [0.01686666667,0.1216433333,6.945813333,28.40629807]
edgeTactic = [0.01706573168,0.09974876245,0.4901337981,5.841367469]

plt.plot(x, noTactic, '#ff7f00', marker="o", markersize=markersize, label="Baseline")
plt.plot(x, noEdge, '#377eb8', marker="s", markersize=markersize, label="No Edge")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Switches', fontsize=20)
plt.ylabel('Avg. Synthesis Time per Class(s)', fontsize=20)

plt.grid()
plt.savefig('linkTopology.eps', format='eps', dpi=1000,  bbox_inches='tight')

dcFig = plt.figure(6)
# Divide and Conquer
speedup = [0.1976315682, 0.4577009344, 0.5377335584, 0.5669575579, 0.6591664453, 0.7049127781, 0.7351070968, 0.800145669, 0.8025833074, 0.9598441312, 0.964727119, 0.9733308864, 0.9733308864, 0.9875814116, 0.9883675111, 0.9883675111, 0.9958673145, 0.9985793792, 1.004670878, 1.012736953, 1.012736953, 1.058836981, 1.104385447, 1.122487297, 1.238680996, 1.25630459, 1.311549326, 1.360240724, 1.36988298, 1.373538053, 1.392101687, 1.398212167, 1.402861377, 1.41148375, 1.477129888, 1.503615798, 1.576835911, 1.7330997, 1.74230301, 1.775858621, 1.830222248, 1.830222248, 1.898015696, 1.915434432, 1.915434432, 1.96579324, 1.985443234, 2.019986643, 2.038286198, 2.038286198, 2.054403506, 2.061307045, 2.12324991, 2.153663175, 2.153663175, 2.17856168, 2.228181006, 2.290710806, 2.641014809, 2.682647899, 2.727936098, 2.885915364, 2.885915364, 2.89063593, 3.171713749, 3.171713749, 3.246657219, 3.270730651, 3.463441287, 3.494842611, 3.537988761, 3.537988761, 3.940502038, 5.310864861, 6.268776604, 6.611002599, 6.611002599, 8.185615374, 12.09321882, 12.1855005, 14.18411328, 19.60053303]
frequency = [0.01219512195, 0.0243902439, 0.03658536585, 0.0487804878, 0.06097560976, 0.07317073171, 0.08536585366, 0.09756097561, 0.1097560976, 0.1219512195, 0.1341463415, 0.1463414634, 0.1585365854, 0.1707317073, 0.1829268293, 0.1951219512, 0.2073170732, 0.2195121951, 0.2317073171, 0.243902439, 0.256097561, 0.2682926829, 0.2804878049, 0.2926829268, 0.3048780488, 0.3170731707, 0.3292682927, 0.3414634146, 0.3536585366, 0.3658536585, 0.3780487805, 0.3902439024, 0.4024390244, 0.4146341463, 0.4268292683, 0.4390243902, 0.4512195122, 0.4634146341, 0.4756097561, 0.487804878, 0.5, 0.512195122, 0.5243902439, 0.5365853659, 0.5487804878, 0.5609756098, 0.5731707317, 0.5853658537, 0.5975609756, 0.6097560976, 0.6219512195, 0.6341463415, 0.6463414634, 0.6585365854, 0.6707317073, 0.6829268293, 0.6951219512, 0.7073170732, 0.7195121951, 0.7317073171, 0.743902439, 0.756097561, 0.7682926829, 0.7804878049, 0.7926829268, 0.8048780488, 0.8170731707, 0.8292682927, 0.8414634146, 0.8536585366, 0.8658536585, 0.8780487805, 0.8902439024, 0.9024390244, 0.9146341463, 0.9268292683, 0.9390243902, 0.9512195122, 0.9634146341, 0.9756097561, 0.987804878, 1]


plt.plot(speedup, frequency, '#377eb8')
plt.xlabel('Non-DC / DC Synthesis Time', fontsize=20)
plt.ylabel('Cumulative Frequency', fontsize=20)

plt.xlim(xmax=5)
plt.grid()
plt.savefig('dcSynthesis.eps', format='eps', dpi=1000,  bbox_inches='tight')