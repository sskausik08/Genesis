# Color Scheme
#e41a1c
#377eb8
#4daf4a
#984ea3
#ff7f00
#ffff33
#f781bf

import numpy as np
import matplotlib
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

matplotlib.rcParams['text.usetex'] = True
label_size = 20
matplotlib.rcParams['xtick.labelsize'] = label_size 
matplotlib.rcParams['ytick.labelsize'] = label_size 


def adjustFigAspect(fig,aspect=1):
    '''
    Adjust the subplot parameters so that the figure has the correct
    aspect ratio.
    '''
    xsize,ysize = fig.get_size_inches()
    minsize = min(xsize,ysize)
    xlim = .4*minsize/xsize
    ylim = .4*minsize/ysize
    if aspect < 1:
        xlim *= aspect
    else:
        ylim /= aspect
    fig.subplots_adjust(left=.5-xlim,
                        right=.5+xlim,
                        bottom=.5-ylim,
                        top=.5+ylim)




# mcmcOspfFig = plt.figure(1)
# x = range(200, 1200, 200)
# ionOspfTime = [2.826036562,13.22029387,30.66177595,53.75930157,84.38471965]
# ionOspfTimeDev = [1.306434742,5.339237255,17.35039753,12.7969357,28.06683488]

# ionOspfTimeWorst = [6.625324065,24.20217831,52.20715576,102.0118506,155.8072723]
# ionOspfTimeWorstDev = [3.695985186,9.135339765,20.03381014,29.3882802,42.76292523]

# fatOspfTime = [3.849331415,29.72222464,91.95010151,143.8896235,256.4885268]
# fatOspfTimeDev = [2.940273538,12.82948726,29.2540355,46.86148018,73.02557615]

# fatOspfTimeWorst = [4.72883755,30.72432349,84.91012555,132.2256593,211.6510137]
# fatOspfTimeWorstDev = [2.825310883,18.35972093,57.95030373,67.09457017,158.4882292]

markersize = 11

# plt.xlim(xmin=190, xmax=1010)

# plt.plot(x, ionOspfTime, '#ff7f00', marker="o", markersize=markersize, label="Best (Ion)")
# plt.errorbar(x, ionOspfTime, color='#ff7f00', yerr=ionOspfTimeDev, linestyle="None")
# plt.plot(x, ionOspfTimeWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
# plt.errorbar(x, ionOspfTimeWorst, color='#ff7f00',  yerr=ionOspfTimeWorstDev, linestyle="None")

# plt.plot(x, fatOspfTime, '#377eb8',marker="D", markersize=markersize, label="Best (Fat-8)")
# plt.errorbar(x, fatOspfTime, color='#377eb8', yerr=fatOspfTimeDev, linestyle="None")
# plt.plot(x, fatOspfTimeWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
# plt.errorbar(x, fatOspfTimeWorst, color='#377eb8', yerr=fatOspfTimeWorstDev, linestyle="None")

# plt.legend(loc='upper left', frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('OSPF Synthesis Time', fontsize=20)

# plt.grid()
# plt.savefig('ospfSynthesisTimeMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

# mcmcConfigFig = plt.figure(2)

#
# ionConf = [110,221.8,321.1,462.1,563.6]
# ionConfDev = [14.78738201,20.31748016,34.67123789,54.41062203,68.61824217]

# ionConfWorst = [171.5909091,319.45,473.25,632.05,780.85]
# ionConfWorstDev = [24.22249858,27.65477973,39.76758135,49.87191489,72.04769984]

# fatConf = [559,1182.88,1851.45,2500.85,3118.45]
# fatConfDev = [57.86281417,101.4627682,165.4074634,183.419357,230.2873434]

# fatConfWorst = [788.15,1638.72,2486.8,3337,4124.5]
# fatConfWorstDev = [49.32947768,64.56683875,90.26662261,80.51413737,146.7394755]

# markersize=11

# plt.xlim(xmin=190, xmax=1010)

# plt.plot(x, ionConf, '#ff7f00', marker="o", markersize=markersize, label="Best (Ion)")
# plt.errorbar(x, ionConf, color='#ff7f00', yerr=ionConfDev, linestyle="None")
# plt.plot(x, ionConfWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
# plt.errorbar(x, ionConfWorst, color='#ff7f00', yerr=ionConfWorstDev, linestyle="None")

# plt.plot(x, fatConf, '#377eb8',marker="D", markersize=markersize, label="Best (Fat-8)")
# plt.errorbar(x, fatConf, color='#377eb8', yerr=fatConfDev, linestyle="None")
# plt.plot(x, fatConfWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
# plt.errorbar(x, fatConfWorst, color='#377eb8', yerr=fatConfWorstDev, linestyle="None")

# plt.legend(loc='upper left', frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('Configuration Overhead', fontsize=20)

# plt.grid()
# plt.savefig('confMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

# mcmcTRLFig = plt.figure(3)
# x = range(200, 1200, 200)
# ionTRL = [7.727272727,25.85,44.15,60.85,89.85]
# ionTRLDev = [4.495307799,7.97545577,15.44182632,11.00370751,20.96431806]

# ionTRLWorst = [15.18181818,44.4,77.75,111.7,160.6]
# ionTRLWorstDev = [5.142135592,12.57147984,20.45502126,15.93110166,22.73045719]

# fatTRL = [14.5,65.56,135.25,194,271.4]
# fatTRLDev = [7.749363302,20.91666003,39.38858371,56.34293492,56.00601471]

# fatTRLWorst = [32.55,120.56,219.6,321.2,447.95]
# fatTRLWorstDev = [11.76737238,26.88723365,46.04162876,49.8160828,91.88750273]

# plt.xlim(xmin=190, xmax=1010)

# plt.plot(x, ionTRL, '#ff7f00',marker="o", markersize=markersize, label="Best (Ion)")
# plt.errorbar(x, ionTRL, color='#ff7f00', yerr=ionTRLDev, linestyle="None")
# plt.plot(x, ionTRLWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
# plt.errorbar(x, ionTRLWorst, color='#ff7f00',   yerr=ionTRLWorstDev, linestyle="None")

# plt.plot(x, fatTRL, '#377eb8', marker="D", markersize=markersize, label="Best (Fat-8)")
# plt.errorbar(x, fatTRL, color='#377eb8', yerr=fatTRLDev, linestyle="None")
# plt.plot(x, fatTRLWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
# plt.errorbar(x, fatTRLWorst, color='#377eb8', yerr=fatTRLWorstDev, linestyle="None")

# plt.legend(loc='upper left', frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('Total Resilience Loss (TRL)', fontsize=20)

# plt.grid()
# plt.savefig('TRLMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

mcmcRatioFig = plt.figure(4)

x = range(200, 1200, 200)
fatBGP = [0.5269179799,0.6517081949,0.6832602247,0.7071751691,0.7223716153]
#ionTRLDev = [0.2497695343,0.1444746083,0.1113659797,0.1181381913,0.09257034323]

fatSR = [1.761261467,0.9587403338,0.827105564,0.6978998297,0.6535906463]

plt.xlim(xmin=190, xmax=1010)
plt.ylim(ymin=0, ymax=2)

plt.plot(x, fatBGP, '#4daf4a',marker="D", markersize=markersize, label="BGP Ratio (Fat-8)")
# plt.errorbar(x, ionTRL, color='#4daf4a', yerr=ionTRLDev, linestyle="None")
# plt.plot(x, ionConf, '#377eb8',marker="^", markersize=markersize, label="Conf Ratio (Ion)")
# plt.errorbar(x, ionConf, color='#377eb8', yerr=ionConfDev, linestyle="None")

plt.plot(x, fatSR, '#ff7f00', marker="o", markersize=markersize, label="SR Ratio (Fat-8)")
# plt.errorbar(x, fatTRL, color='#ff7f00', yerr=fatTRLDev, linestyle="None")
# plt.plot(x, fatConf, '#984ea3', marker="s", markersize=markersize, label="Conf Ratio (Fat-8)")
# plt.errorbar(x, fatConf, color='#984ea3', yerr=fatConfDev, linestyle="None")

plt.legend(loc='upper left', mode="expand", ncol=2, frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Ratio', fontsize=20)

plt.grid()
plt.savefig('ratioMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')


# ospfTimeFig = plt.figure(5)
# x = range(25, 225, 25)

# ionTime = [0.01749955864,0.07191940294,0.1476163773,0.2930797994,0.4789884697,0.6663588462,0.9209012076,1.15511427]
# ionTimeDev = [0.009488063792,0.02699395579,0.06919721199,0.08314940039,0.1465465516,0.2193709322,0.241433187,0.2587683784]
# ionTime = [p*t for p,t in zip(x,ionTime)]
# ionTimeDev = [p*t for p,t in zip(x,ionTimeDev)]

# fat6Time =  [0.04263912741,0.3389375772,2.070554649,4.668311028,7.679610742,10.82252409,12.59832289,15.4758605]
# fat6TimeDev = [0.02472738843,0.1789896801,1.013203957,0.9042154791,1.170098253,0.9448482264,1.129939945,1.686918172]
# fat6Time = [p*t for p,t in zip(x,fat6Time)]
# fat6TimeDev = [p*t for p,t in zip(x,fat6TimeDev)]


# fat4Time =  [0.02526011467,0.1084675329,0.2238150358,0.3463366435,0.4060181068,0.4730815102,0.5297162876,0.598101095]
# fat4TimeDev = [0.01213860087,0.0303217649,0.03861147015,0.0453386104,0.05625595682,0.04384863373,0.05146077266,0.07802651106]
# fat4Time = [p*t for p,t in zip(x,fat4Time)]
# fat4TimeDev = [p*t for p,t in zip(x,fat4TimeDev)]

# plt.xlim(xmin=15, xmax=210)
# plt.yscale('log')

# plt.plot(x, ionTime, '#4daf4a',marker="D", markersize=markersize, label="Geant (40)")
# plt.errorbar(x, ionTime, color='#4daf4a', yerr=ionTimeDev, linestyle="None")

# plt.plot(x, fat4Time, '#377eb8', marker="s", markersize=markersize, label="Fat-4 (20)")
# plt.errorbar(x, fat4Time, color='#377eb8', yerr=fat4TimeDev, linestyle="None")

# plt.plot(x, fat6Time, '#ff7f00', marker="o", markersize=markersize, label="Fat-6 (45)")
# plt.errorbar(x, fat6Time, color='#ff7f00', yerr=fat6TimeDev, linestyle="None")


# plt.legend(loc='upper left', frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('OSPF Synthesis Time(log s)', fontsize=20)

# plt.grid()
# plt.savefig('ospfTime.eps', format='eps', dpi=1000, bbox_inches='tight')

# ospfRFFig = plt.figure(6)
# x = range(25, 225, 25)

# fat6RF = [6.966666667,41.23333333,173.0333333,434.3157895,742.0333333,1107.925926,1401.571429,1861.85]
# fat6RFDev = [4.902380374,13.54859284,63.37381344,71.21723623,78.4093957,83.4823454,94.13915176,134.8415347]

# ionRF =  [4.78,25.28571429,50.24,99.45070423,157.48,224.5428571,320.4390244,406.92]
# ionRFDev = [3.677232766,8.881086983,18.92580573,29.9493805,38.19832243,60.74815813,63.74168525,68.83397358]

# fat4RF =  [12.85,61.4,142.25,248.7,332.5,419.05,501.5,594.9]
# fat4RFDev = [6.722115895,15.08711545,22.1332686,32.69170183,38.80518142,39.33054926,44.07469736,68.99725395]

# plt.xlim(xmin=15, xmax=210)
# plt.yscale('log')

# plt.plot(x, ionRF, '#4daf4a',marker="D", markersize=markersize, label="Geant (40)")
# plt.errorbar(x, ionRF, color='#4daf4a', yerr=ionRFDev, linestyle="None")

# plt.plot(x, fat4RF, '#377eb8', marker="o", markersize=markersize, label="Fat-4 (20)")
# plt.errorbar(x, fat4RF, color='#377eb8', yerr=fat4RFDev, linestyle="None")

# plt.plot(x, fat6RF, '#ff7f00', marker="o", markersize=markersize, label="Fat-6 (45)")
# plt.errorbar(x, fat6RF, color='#ff7f00', yerr=fat6RFDev, linestyle="None")

# plt.legend(loc='upper left', frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('Total number of Route-Filters (log n)', fontsize=20)

# plt.grid()
# plt.savefig('ospfRF.eps', format='eps', dpi=1000, bbox_inches='tight')

# ospfAvgResFig = plt.figure(7)
# x = range(25, 225, 25)

# ionAvgRes = [0.828,0.8251428571,0.7970666667,0.7521126761,0.74192,0.7087619048,0.6730313589,0.6447]
# ionAvgResDev = [0.2500285698,0.1814494209,0.1528632843,0.09906585822,0.08725936942,0.08120305442,0.0666334744,0.06690238091]
# ionBestRes = [21.14,44.35714286,65.56,86.12676056,109.28,130.9285714,151.3658537,172.5]

# fat6AvgRes =  [3.16,3.001333333,2.901777778,2.72,2.319733333,1.964691358,1.832653061,1.5545]
# fat6AvgResDev = [0.3528015951,0.3403419511,0.224519467,0.2138015695,0.1985601504,0.1381540675,0.0930914539,0.1425971506]
# fat6BestRes = [80.5,157.5,237.3,328.8421053,394.8,474.3333333,557.3214286,633.1]

# fat4AvgRes =  [1.476,1.261,1.086666667,0.938,0.8628,0.785,0.7557142857,0.717]
# fat4AvgResDev = [0.233201968,0.1280583748,0.1298852395,0.1101482255,0.1131154976,0.07114354158,0.07503096389,0.08324662155]
# fat4BestRes = [40.9,78.6,121.2,163.3,201.8,243.8,282.5,326.7]


# plt.xlim(xmin=15, xmax=210)
# plt.ylim(ymin=0, ymax=5)

# plt.plot(x, ionAvgRes, '#4daf4a',marker="D", markersize=markersize, label="Syn (40)")
# plt.plot(x, [res/x1 for x1,res in zip(x, ionBestRes)], '#4daf4a', linestyle='--', linewidth=4, marker="D", markersize=8, label="Best (40)")
# plt.errorbar(x, ionAvgRes, color='#4daf4a', yerr=ionAvgResDev, linestyle="None")

# plt.plot(x, fat4AvgRes, '#377eb8', marker="s", markersize=markersize, label="Syn (20)")
# plt.plot(x, [res/x1 for x1,res in zip(x, fat4BestRes)], '#377eb8', linestyle='--', linewidth=4, marker="s", markersize=8, label="Best (20)")
# plt.errorbar(x, fat4AvgRes, color='#377eb8', yerr=fat4AvgResDev, linestyle="None")


# plt.plot(x, fat6AvgRes, '#ff7f00', marker="o", markersize=markersize, label="Syn (45)")
# plt.plot(x, [res/x1 for x1,res in zip(x, fat6BestRes)], '#ff7f00', linestyle='--', linewidth=4, marker="o", markersize=8, label="Best (45)")
# plt.errorbar(x, fat6AvgRes, color='#ff7f00', yerr=fat6AvgResDev, linestyle="None")


# plt.legend(loc='upper right', mode="expand", ncol=3, frameon=False, fontsize=18)

# plt.xlabel('Number of Paths', fontsize=20)
# plt.ylabel('Average endpoint resilience', fontsize=20)

# plt.grid()
# plt.savefig('ospfAvgRes.eps',  format='eps', dpi=1000, bbox_inches='tight')

#ospfWaypointFig = plt.figure(1)
ospfWaypointFig, (ax1, ax2, ax3) = plt.subplots(1, 3, sharey=True)
adjustFigAspect(ospfWaypointFig, 4.5)
x = range(10, 90, 10)
xticks = range(10, 90, 20)
yticks = [0, 1, 10, 100, 1000]
zeroes = [1 for a in range(8)]
genesisTime = [1.905232944, 4.054856551, 6.447951472, 8.774414492, 11.60772855, 14.57009258,18.05601811, 21.1040017]
totTime = [2.650796689,5.545891339,15.29532384,31.4204547,97.32999361,209.9557621,338.6178232,437.1733794]
#totTime = [a + b for a,b in zip(genesisTime,zeppelinTime)]

ax1.set_xlim([10, 80])
ax1.set_xticks(xticks)
ax1.set_yscale('log')

ax1.plot(x, genesisTime, '#ff7f00')
ax1.plot(x, totTime, '#377eb8',)

ax1.fill_between(x, genesisTime, totTime, color='#377eb8', alpha='0.5', label="Zeppelin")
ax1.fill_between(x, 1, genesisTime, color='#ff7f00', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax1.set_ylabel('Synthesis Time (s)', fontsize=5)

ax1.grid()

genesisTime = [1.898177683,4.137906945,6.411716133,8.66710724,11.57976503,14.78331525,17.91517298,21.24656556]
totTime = [3.339358291,8.092288089,30.90892007,101.4620721,284.8738477,531.9663218,743.310784,923.8451524]

ax2.set_xlim([10, 80])
ax2.set_xticks(xticks)
ax2.set_yscale('log')

ax2.plot(x, genesisTime, '#ff7f00')
ax2.plot(x, totTime, '#377eb8',)

z = ax2.fill_between(x, genesisTime, totTime, color='#377eb8', alpha='0.5', label="Zeppelin")
g = ax2.fill_between(x, 1, genesisTime, color='#ff7f00', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax2.set_xlabel('Number of Paths', fontsize=20)
ax2.grid()

genesisTime = [1.686398292,4.115126556,6.254837424,8.705678749,11.5079913,14.68902937,17.80753183,21.22884498]
totTime = [4.920500342,13.93155347,47.64036253,181.4483577,448.8050332,921.0370142,1526.903791,2082.716671]

ax3.set_xlim([10, 80])
ax3.set_xticks(xticks)
ax3.set_yscale('log')

ax3.plot(x, genesisTime, '#ff7f00')
ax3.plot(x, totTime, '#377eb8',)

ax3.fill_between(x, genesisTime, totTime, color='#377eb8', alpha='0.5', label="Zeppelin")
ax3.fill_between(x, 1, genesisTime, color='#ff7f00', alpha='0.5', label="Genesis")

ax3.grid()
# ax2.grid()
plt.legend(['Genesis','Zeppelin'], fontsize=13,  ncol=2, loc='upper center', 
    bbox_to_anchor=[-0.7, 1.50], columnspacing=1.0, labelspacing=0.0,handletextpad=0.0, 
    handlelength=1.5, fancybox=True)
plt.savefig('ospfwaypoint.eps', format='eps', dpi=1000, bbox_inches='tight')

ospfIsolationFig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
adjustFigAspect(ospfIsolationFig, 4)

x = range(10, 90, 10)
xticks = range(10, 90, 20)
zeroes = [1 for a in range(8)]
genesisTime = [2.89080843,6.00545728,9.226121505,12.25871157,15.34863245,18.33711504,21.43881194,24.63348559]
totTime = [3.466053895,6.866023487,10.80940593,15.62154008,21.4005797,29.08060994,42.86516188,73.06307]

ax1.set_xlim([10, 80])
ax1.set_xticks(xticks)

ax1.plot(x, genesisTime, '#ff7f00')
ax1.plot(x, totTime, '#377eb8',)

ax1.fill_between(x, genesisTime, totTime, color='#377eb8', alpha='0.5', label="Zeppelin")
ax1.fill_between(x, 0, genesisTime, color='#ff7f00', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax1.set_ylabel('Synthesis Time (s)', fontsize=5)

ax1.grid()
x = range(20, 100, 20)
genesisTime = [8.910769089,17.94230479,26.42362858,35.19051689]
totTime = [9.795185072,21.18261655,39.06264416,77.62741683]

ax2.set_xlim([20, 80])
ax2.set_xticks(x)

ax2.plot(x, genesisTime, '#ff7f00')
ax2.plot(x, totTime, '#377eb8',)

z = ax2.fill_between(x, genesisTime, totTime, color='#377eb8', alpha='0.5', label="Zeppelin")
g = ax2.fill_between(x, 0, genesisTime, color='#ff7f00', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax2.set_xlabel('Number of Paths', fontsize=20)
ax2.grid()
plt.legend(['Genesis','Zeppelin'], fontsize=13,  ncol=2, loc='upper center', 
    bbox_to_anchor=[-0.35, 1.50], columnspacing=1.0, labelspacing=0.0,handletextpad=0.0, 
    handlelength=1.5, fancybox=True)
plt.savefig('ospfisolation.eps', format='eps', dpi=1000, bbox_inches='tight')


zepres10W = [0.5566037736,0.8015873016,0.674796748,0.7863247863,0.6732673267,0.6725663717,0.55,0.7234042553,0.7555555556,0.7065217391,0.7777777778,0.7169811321,0.5894736842,0.8172043011,0.7232142857,0.6451612903,0.7272727273,0.7976190476,0.698630137,0.75,0.6805555556,0.5882352941,0.7333333333,0.7040816327,0.8072289157,0.7532467532,0.7340425532,0.6868686869,0.5842696629,0.6082474227,0.84,0.8035714286,0.7413793103,0.6344086022,0.6326530612,0.7582417582,0.4719101124,0.7431192661,0.6989247312,0.6666666667,0.7386363636,0.6129032258,0.7642276423,0.6632653061,0.5979381443,0.6829268293,0.8021978022,0.5806451613,0.7157894737,0.7222222222,0.7808219178,0.7325581395,0.900990099,0.7608695652,0.5596330275,0.72,0.7978723404,0.6404494382,0.6226415094,0.6460176991,0.5494505495,0.618556701,0.6136363636,0.725,0.6043956044,0.7848101266,0.6842105263,0.6575342466,0.7553191489,0.5326086957,0.6442307692,0.7391304348,0.7472527473,0.6458333333,0.8796296296,0.7157894737,0.8590604027,0.7070707071,0.7222222222,0.7884615385,0.6460176991,0.8130841122,0.8148148148,0.7394957983,0.6857142857,0.7333333333,0.6571428571,0.6111111111,0.6666666667,0.7974683544,0.8275862069,0.7361111111,0.7162162162]
zepres10WR = [0.9405405405,0.9453551913,0.9402173913,0.994047619,0.995,0.9704433498,0.9684210526,0.955,0.9757281553,0.9659090909,0.9590643275,0.9494382022,0.9888268156,0.9554140127,0.9701492537,0.9754901961,0.9329608939,0.968503937,0.9880239521,0.976744186,0.9942196532,0.9888268156,0.9677419355,0.9900497512,0.9870967742,0.9943181818,0.9404761905,0.975,0.9805194805,1,1,0.9903846154,0.9816513761,0.9841269841,0.9623655914,0.9730941704,0.9849246231,0.9734042553,0.9923664122,0.9885057471,1,0.9666666667,0.963190184,0.9949238579,0.9907834101,1,0.9651162791,0.9902912621,1,0.9950980392,0.9870967742,0.9432624113,0.9900497512,1,0.9896373057,0.98,0.9698795181,0.9834254144,0.9770114943,0.9777777778,1,0.995412844,0.9937106918,0.9943181818,0.9700598802,0.9936708861,0.9431818182,0.9929078014,0.9585798817,0.9349112426,0.9943502825,0.9790575916,0.9130434783,0.9277108434,1,0.9378531073,0.9510869565,1,0.981981982,0.9824561404,0.9777777778,0.979020979,0.9878787879,0.99375,0.9622641509,0.9805194805,0.9842105263,0.9795918367,0.9951690821,1,0.9824561404,0.9795918367,0.9756097561]
zepres10P = [0.3409090909, 0.4285714286, 0.3854166667, 0.4777777778, 0.5102040816, 0.5319148936, 0.402173913, 0.6020408163, 0.5625, 0.4772727273, 0.5, 0.4642857143, 0.4756097561, 0.4418604651, 0.4545454545, 0.2727272727, 0.3510638298, 0.3372093023, 0.5138888889, 0.5, 0.5675675676, 0.5540540541, 0.4459459459, 0.4222222222, 0.4625, 0.421686747, 0.5494505495, 0.3595505618, 0.5368421053, 0.4395604396, 0.5, 0.5465116279, 0.5833333333, 0.3111111111, 0.4886363636, 0.4117647059, 0.3614457831, 0.5348837209, 0.4186046512, 0.4487179487, 0.4756097561, 0.4588235294, 0.3950617284, 0.525, 0.3409090909, 0.3875, 0.5714285714, 0.512195122, 0.4137931034, 0.5053763441, 0.5476190476, 0.5217391304, 0.5913978495, 0.4946236559, 0.4352941176, 0.5161290323, 0.5308641975, 0.4137931034, 0.3908045977, 0.4777777778, 0.4615384615, 0.4831460674, 0.3707865169, 0.5697674419, 0.3793103448, 0.4943820225, 0.5934065934, 0.4946236559, 0.4880952381, 0.3375, 0.4555555556, 0.575, 0.575, 0.358974359, 0.4943820225, 0.575, 0.5119047619, 0.5, 0.4712643678, 0.4819277108, 0.4705882353, 0.4941176471, 0.5, 0.4512195122, 0.4523809524, 0.5319148936, 0.5308641975, 0.3647058824, 0.4683544304, 0.6075949367, 0.5189873418, 0.5308641975, 0.6233766234]

ospfResilienceFig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
adjustFigAspect(ospfResilienceFig, 2)

ax1.set_xlim([0, 1])
ax1.set_ylim([0.8, 1])

ax1.scatter(zepres10W, zepres10WR, marker="D", s=3, color='#ff7f00')
ax1.scatter(zepres10P, zepres10WR, marker="^", s=3, color='#377eb8')


zepres20W=[0.5212765957, 0.5837563452, 0.5555555556, 0.6585365854, 0.5531914894, 0.5476190476, 0.6458333333, 0.7384615385, 0.7, 0.8092105263, 0.5437788018, 0.4945054945, 0.64, 0.6050955414, 0.6448087432, 0.5806451613, 0.6826923077, 0.6397515528, 0.6944444444, 0.6568047337, 0.6779661017, 0.5705521472, 0.7041420118, 0.5663265306, 0.643902439, 0.5898876404, 0.6585365854, 0.5588235294, 0.5873015873, 0.5833333333, 0.6833333333, 0.6285714286, 0.6363636364, 0.5384615385, 0.6318681319, 0.6560509554, 0.7806451613, 0.6226415094, 0.6627218935, 0.5953757225, 0.6440677966, 0.6607142857, 0.6097560976, 0.6741573034, 0.717791411, 0.6467391304, 0.5454545455, 0.5609756098, 0.4785276074, 0.625, 0.6075268817, 0.6217948718, 0.7362637363, 0.7102272727, 0.5591397849, 0.5838509317, 0.582010582, 0.5857988166, 0.6467391304, 0.6790123457, 0.6073619632, 0.6448087432, 0.5744680851, 0.6559139785, 0.6761363636, 0.6337209302, 0.6793478261, 0.6228571429, 0.608490566, 0.6432160804, 0.6448087432, 0.6258064516, 0.6917808219, 0.6868686869, 0.5783783784, 0.5028571429, 0.6193548387, 0.597826087, 0.619047619, 0.6751592357, 0.7142857143, 0.6098654709, 0.6358695652, 0.6496815287, 0.6723163842, 0.6447368421, 0.6686046512, 0.6507936508, 0.5555555556, 0.7207792208, 0.6369426752, 0.6804733728, 0.5952380952, 0.625, 0.6451612903, 0.6229508197, 0.6582914573, 0.7745098039, 0.6413043478, 0.6397849462]
zepres20WR=[0.9950617284, 0.9765625, 0.9852941176, 0.9772727273, 0.9794871795, 0.99756691, 1, 0.9975247525, 1, 0.9972752044, 0.9831325301, 0.9975124378, 0.9841688654, 0.9837398374, 0.9945504087, 0.9899749373, 1, 0.9810810811, 0.9948979592, 0.9925187032, 0.9742930591, 0.9825436409, 1, 0.9977678571, 0.9663212435, 0.9976470588, 0.9791666667, 0.9722222222, 0.9976019185, 0.9756097561, 0.9817232376, 0.9867724868, 0.9882352941, 0.9975062344, 0.9954022989, 0.9927536232, 0.9898477157, 1, 0.9976359338, 0.9809976247, 0.9949494949, 0.9873417722, 0.9931034483, 0.986631016, 0.9922879177, 0.9976019185, 1, 0.9766081871, 0.9944751381, 0.9755434783, 0.9580246914, 0.9566473988, 0.9761904762, 0.9977375566, 0.9613402062, 0.9737609329, 1, 0.9850746269, 0.9738219895, 0.9796954315, 0.9895287958, 0.9920634921, 0.9932126697, 0.9571428571, 0.9950980392, 0.9921465969, 0.9869791667, 0.9693593315, 0.9823677582, 0.9884526559, 0.9927710843, 0.9895561358, 0.9867021277, 1, 0.9743589744, 0.9908466819, 0.9975903614, 0.9803439803, 0.9956616052, 1, 0.9873096447, 1, 0.9933628319, 0.9779614325, 0.9753424658, 0.9607250755, 0.9902676399, 0.9946949602, 0.9925373134, 0.9809069212, 0.9839572193, 0.9831460674, 0.9974160207, 0.9973404255, 0.9867724868, 0.9792746114, 0.9844444444, 0.9880095923, 0.9975961538, 0.9928571429]
zepres20P=[0.3988095238,0.4293785311,0.4736842105,0.5277777778,0.5229885057,0.4588235294,0.4698795181,0.4111111111,0.5182926829,0.450617284,0.3825136612,0.4683544304,0.4810126582,0.4519774011,0.497005988,0.4678362573,0.3631284916,0.549132948,0.4685714286,0.5085714286,0.4689265537,0.4733727811,0.4858757062,0.4545454545,0.4254143646,0.4535519126,0.4411764706,0.4666666667,0.4093567251,0.4831460674,0.5348837209,0.476744186,0.417721519,0.4111111111,0.4352941176,0.5,0.5714285714,0.4085365854,0.462962963,0.4393063584,0.5263157895,0.52,0.3988439306,0.4337349398,0.5117647059,0.3875,0.4367816092,0.4319526627,0.4394904459,0.4792899408,0.5088757396,0.493902439,0.5085714286,0.4910179641,0.5163043478,0.5090909091,0.4674556213,0.4702702703,0.4430379747,0.5120481928,0.4534883721,0.4647058824,0.402173913,0.4096385542,0.4478527607,0.5029239766,0.530726257,0.4262295082,0.4385964912,0.3865030675,0.4413407821,0.5975609756,0.5197740113,0.4198895028,0.5191256831,0.3771428571,0.4649681529,0.4795321637,0.4864864865,0.5182926829,0.5316455696,0.591954023,0.4968553459,0.4777070064,0.5114942529,0.5352941176,0.5212121212,0.5254237288,0.5153374233,0.5029585799,0.4727272727,0.4465408805,0.502994012,0.4240506329,0.4825581395,0.4034090909,0.5406976744,0.4858757062,0.4457142857,0.4113924051,0.4748603352,0.4267515924,0.5,0.5,0.4423076923,0.4125,0.4682080925,0.4237288136,0.4606060606,0.4596273292,0.5086705202,0.4748603352,0.4157303371,0.4615384615,0.4367816092,0.4938271605,0.50625,0.4318181818]
zepres20P=zepres20P[:100]
print len(zepres20WR), len(zepres20P)

ax2.set_xlim([0, 1])
ax2.set_ylim([0.8, 1])

ax2.scatter(zepres20W, zepres20WR, marker="D", s=3, color='#ff7f00')
ax2.scatter(zepres20P, zepres20WR, marker="^", s=3, color='#377eb8')


plt.savefig('ospfresilience.eps', format='eps', dpi=1000, bbox_inches='tight')

# mcmc = plt.figure(2)
# f = open("zep-mcmc.csv")
# x = []
# y = []
# for line in f:
#     fields = line.split("\t")
#     x.append(int(fields[0]))
#     y.append(float(fields[1]))

# plt.plot(x, y, '#ff7f00', marker="o") markersize=markersize,

# plt.xlabel('Iteration')
# plt.ylabel('MCMC Score')

# plt.grid()
# plt.savefig('mcmc.png', format='png', dpi=300, bbox_inches='tight')


