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




mcmcOspfFig = plt.figure(1)
x = range(200, 1200, 200)
ionOspfTime = [2.826036562,13.22029387,30.66177595,53.75930157,84.38471965]
ionOspfTimeDev = [1.306434742,5.339237255,17.35039753,12.7969357,28.06683488]

ionOspfTimeWorst = [6.625324065,24.20217831,52.20715576,102.0118506,155.8072723]
ionOspfTimeWorstDev = [3.695985186,9.135339765,20.03381014,29.3882802,42.76292523]

fatOspfTime = [3.849331415,29.72222464,91.95010151,143.8896235,256.4885268]
fatOspfTimeDev = [2.940273538,12.82948726,29.2540355,46.86148018,73.02557615]

fatOspfTimeWorst = [4.72883755,30.72432349,84.91012555,132.2256593,211.6510137]
fatOspfTimeWorstDev = [2.825310883,18.35972093,57.95030373,67.09457017,158.4882292]

markersize = 11

plt.xlim(xmin=190, xmax=1010)

plt.plot(x, ionOspfTime, '#ff7f00', marker="o", markersize=markersize, label="Best (Ion)")
plt.errorbar(x, ionOspfTime, color='#ff7f00', yerr=ionOspfTimeDev, linestyle="None")
plt.plot(x, ionOspfTimeWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
plt.errorbar(x, ionOspfTimeWorst, color='#ff7f00',  yerr=ionOspfTimeWorstDev, linestyle="None")

plt.plot(x, fatOspfTime, '#377eb8',marker="D", markersize=markersize, label="Best (Fat-8)")
plt.errorbar(x, fatOspfTime, color='#377eb8', yerr=fatOspfTimeDev, linestyle="None")
plt.plot(x, fatOspfTimeWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
plt.errorbar(x, fatOspfTimeWorst, color='#377eb8', yerr=fatOspfTimeWorstDev, linestyle="None")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('OSPF Synthesis Time', fontsize=20)

plt.grid()
plt.savefig('ospfSynthesisTimeMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

mcmcConfigFig = plt.figure(2)
x = range(200, 1200, 200)
ionConf = [110,221.8,321.1,462.1,563.6]
ionConfDev = [14.78738201,20.31748016,34.67123789,54.41062203,68.61824217]

ionConfWorst = [171.5909091,319.45,473.25,632.05,780.85]
ionConfWorstDev = [24.22249858,27.65477973,39.76758135,49.87191489,72.04769984]

fatConf = [559,1182.88,1851.45,2500.85,3118.45]
fatConfDev = [57.86281417,101.4627682,165.4074634,183.419357,230.2873434]

fatConfWorst = [788.15,1638.72,2486.8,3337,4124.5]
fatConfWorstDev = [49.32947768,64.56683875,90.26662261,80.51413737,146.7394755]

markersize=11

plt.xlim(xmin=190, xmax=1010)

plt.plot(x, ionConf, '#ff7f00', marker="o", markersize=markersize, label="Best (Ion)")
plt.errorbar(x, ionConf, color='#ff7f00', yerr=ionConfDev, linestyle="None")
plt.plot(x, ionConfWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
plt.errorbar(x, ionConfWorst, color='#ff7f00', yerr=ionConfWorstDev, linestyle="None")

plt.plot(x, fatConf, '#377eb8',marker="D", markersize=markersize, label="Best (Fat-8)")
plt.errorbar(x, fatConf, color='#377eb8', yerr=fatConfDev, linestyle="None")
plt.plot(x, fatConfWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
plt.errorbar(x, fatConfWorst, color='#377eb8', yerr=fatConfWorstDev, linestyle="None")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Lines of Configuration', fontsize=20)

plt.grid()
plt.savefig('confMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

mcmcTRLFig = plt.figure(3)
x = range(200, 1200, 200)
ionTRL = [7.727272727,25.85,44.15,60.85,89.85]
ionTRLDev = [4.495307799,7.97545577,15.44182632,11.00370751,20.96431806]

ionTRLWorst = [15.18181818,44.4,77.75,111.7,160.6]
ionTRLWorstDev = [5.142135592,12.57147984,20.45502126,15.93110166,22.73045719]

fatTRL = [14.5,65.56,135.25,194,271.4]
fatTRLDev = [7.749363302,20.91666003,39.38858371,56.34293492,56.00601471]

fatTRLWorst = [32.55,120.56,219.6,321.2,447.95]
fatTRLWorstDev = [11.76737238,26.88723365,46.04162876,49.8160828,91.88750273]

plt.xlim(xmin=190, xmax=1010)

plt.plot(x, ionTRL, '#ff7f00',marker="o", markersize=markersize, label="Best (Ion)")
plt.errorbar(x, ionTRL, color='#ff7f00', yerr=ionTRLDev, linestyle="None")
plt.plot(x, ionTRLWorst, '#ff7f00', linestyle='--', marker="^", markersize=markersize, label="Worst (Ion)")
plt.errorbar(x, ionTRLWorst, color='#ff7f00',   yerr=ionTRLWorstDev, linestyle="None")

plt.plot(x, fatTRL, '#377eb8', marker="D", markersize=markersize, label="Best (Fat-8)")
plt.errorbar(x, fatTRL, color='#377eb8', yerr=fatTRLDev, linestyle="None")
plt.plot(x, fatTRLWorst, '#377eb8', linestyle='--', marker="s", markersize=markersize, label="Worst (Fat-8)")
plt.errorbar(x, fatTRLWorst, color='#377eb8', yerr=fatTRLWorstDev, linestyle="None")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Total Loss of Resilience', fontsize=20)

plt.grid()
plt.savefig('TRLMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')

mcmcRatioFig = plt.figure(4)

ionTRL = [0.5211072418,0.591550364,0.5630383916,0.5534444341,0.5584180279]
ionTRLDev = [0.2497695343,0.1444746083,0.1113659797,0.1181381913,0.09257034323]

fatTRL =  [0.4924297224,0.5583962327,0.6494166133,0.6098824146,0.6173405641]
fatTRLDev = [0.2861649555,0.1756585491,0.2639303385,0.1786446427,0.1289398753]

ionConf = [0.6451663308,0.6950191705,0.6793915277,0.731510484,0.7212847146]
ionConfDev = [0.07000478351,0.03891852816,0.05775659742,0.06522387861,0.05078881237]

fatConf = [0.7087146829,0.721486085,0.7444977524,0.7492399511,0.7559644731]
fatConfDev = [0.05087937556,0.04968711413,0.06099461023,0.04877063637,0.04660650303]

plt.xlim(xmin=190, xmax=1010)
plt.ylim(ymin=0, ymax=1.2)

plt.plot(x, ionTRL, '#4daf4a',marker="D", markersize=markersize, label="TRL Ratio (Ion)")
plt.errorbar(x, ionTRL, color='#4daf4a', yerr=ionTRLDev, linestyle="None")
plt.plot(x, ionConf, '#377eb8',marker="^", markersize=markersize, label="Conf Ratio (Ion)")
plt.errorbar(x, ionConf, color='#377eb8', yerr=ionConfDev, linestyle="None")

plt.plot(x, fatTRL, '#ff7f00', marker="o", markersize=markersize, label="TRL Ratio  (Fat-8)")
plt.errorbar(x, fatTRL, color='#ff7f00', yerr=fatTRLDev, linestyle="None")
plt.plot(x, fatConf, '#984ea3', marker="s", markersize=markersize, label="Conf Ratio (Fat-8)")
plt.errorbar(x, fatConf, color='#984ea3', yerr=fatConfDev, linestyle="None")

plt.legend(loc='upper left', mode="expand", ncol=2, frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Ratio', fontsize=20)

plt.grid()
plt.savefig('ratioMCMC.eps', format='eps', dpi=1000, bbox_inches='tight')


ospfTimeFig = plt.figure(5)
x = range(25, 225, 25)

ionTime = [0.01749955864,0.07191940294,0.1476163773,0.2930797994,0.4789884697,0.6663588462,0.9209012076,1.15511427]
ionTimeDev = [0.009488063792,0.02699395579,0.06919721199,0.08314940039,0.1465465516,0.2193709322,0.241433187,0.2587683784]
ionTime = [p*t for p,t in zip(x,ionTime)]
ionTimeDev = [p*t for p,t in zip(x,ionTimeDev)]

fat6Time =  [0.04263912741,0.3389375772,2.070554649,4.668311028,7.679610742,10.82252409,12.59832289,15.4758605]
fat6TimeDev = [0.02472738843,0.1789896801,1.013203957,0.9042154791,1.170098253,0.9448482264,1.129939945,1.686918172]
fat6Time = [p*t for p,t in zip(x,fat6Time)]
fat6TimeDev = [p*t for p,t in zip(x,fat6TimeDev)]


fat4Time =  [0.02526011467,0.1084675329,0.2238150358,0.3463366435,0.4060181068,0.4730815102,0.5297162876,0.598101095]
fat4TimeDev = [0.01213860087,0.0303217649,0.03861147015,0.0453386104,0.05625595682,0.04384863373,0.05146077266,0.07802651106]
fat4Time = [p*t for p,t in zip(x,fat4Time)]
fat4TimeDev = [p*t for p,t in zip(x,fat4TimeDev)]

plt.xlim(xmin=15, xmax=210)
plt.yscale('log')

plt.plot(x, ionTime, '#4daf4a',marker="D", markersize=markersize, label="Geant (40)")
plt.errorbar(x, ionTime, color='#4daf4a', yerr=ionTimeDev, linestyle="None")

plt.plot(x, fat4Time, '#377eb8', marker="s", markersize=markersize, label="Fat-4 (20)")
plt.errorbar(x, fat4Time, color='#377eb8', yerr=fat4TimeDev, linestyle="None")

plt.plot(x, fat6Time, '#ff7f00', marker="o", markersize=markersize, label="Fat-6 (45)")
plt.errorbar(x, fat6Time, color='#ff7f00', yerr=fat6TimeDev, linestyle="None")


plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('OSPF Synthesis Time(log s)', fontsize=20)

plt.grid()
plt.savefig('ospfTime.eps', format='eps', dpi=1000, bbox_inches='tight')

ospfRFFig = plt.figure(6)
x = range(25, 225, 25)

fat6RF = [6.966666667,41.23333333,173.0333333,434.3157895,742.0333333,1107.925926,1401.571429,1861.85]
fat6RFDev = [4.902380374,13.54859284,63.37381344,71.21723623,78.4093957,83.4823454,94.13915176,134.8415347]

ionRF =  [4.78,25.28571429,50.24,99.45070423,157.48,224.5428571,320.4390244,406.92]
ionRFDev = [3.677232766,8.881086983,18.92580573,29.9493805,38.19832243,60.74815813,63.74168525,68.83397358]

fat4RF =  [12.85,61.4,142.25,248.7,332.5,419.05,501.5,594.9]
fat4RFDev = [6.722115895,15.08711545,22.1332686,32.69170183,38.80518142,39.33054926,44.07469736,68.99725395]

plt.xlim(xmin=15, xmax=210)
plt.yscale('log')

plt.plot(x, ionRF, '#4daf4a',marker="D", markersize=markersize, label="Geant (40)")
plt.errorbar(x, ionRF, color='#4daf4a', yerr=ionRFDev, linestyle="None")

plt.plot(x, fat4RF, '#377eb8', marker="o", markersize=markersize, label="Fat-4 (20)")
plt.errorbar(x, fat4RF, color='#377eb8', yerr=fat4RFDev, linestyle="None")

plt.plot(x, fat6RF, '#ff7f00', marker="o", markersize=markersize, label="Fat-6 (45)")
plt.errorbar(x, fat6RF, color='#ff7f00', yerr=fat6RFDev, linestyle="None")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Total number of Route-Filters (log n)', fontsize=20)

plt.grid()
plt.savefig('ospfRF.eps', format='eps', dpi=1000, bbox_inches='tight')

ospfAvgResFig = plt.figure(7)
x = range(25, 225, 25)

ionAvgRes = [0.828,0.8251428571,0.7970666667,0.7521126761,0.74192,0.7087619048,0.6730313589,0.6447]
ionAvgResDev = [0.2500285698,0.1814494209,0.1528632843,0.09906585822,0.08725936942,0.08120305442,0.0666334744,0.06690238091]
ionBestRes = [21.14,44.35714286,65.56,86.12676056,109.28,130.9285714,151.3658537,172.5]

fat6AvgRes =  [3.16,3.001333333,2.901777778,2.72,2.319733333,1.964691358,1.832653061,1.5545]
fat6AvgResDev = [0.3528015951,0.3403419511,0.224519467,0.2138015695,0.1985601504,0.1381540675,0.0930914539,0.1425971506]
fat6BestRes = [80.5,157.5,237.3,328.8421053,394.8,474.3333333,557.3214286,633.1]

fat4AvgRes =  [1.476,1.261,1.086666667,0.938,0.8628,0.785,0.7557142857,0.717]
fat4AvgResDev = [0.233201968,0.1280583748,0.1298852395,0.1101482255,0.1131154976,0.07114354158,0.07503096389,0.08324662155]
fat4BestRes = [40.9,78.6,121.2,163.3,201.8,243.8,282.5,326.7]


plt.xlim(xmin=15, xmax=210)
plt.ylim(ymin=0, ymax=5)

plt.plot(x, ionAvgRes, '#4daf4a',marker="D", markersize=markersize, label="Syn (40)")
plt.plot(x, [res/x1 for x1,res in zip(x, ionBestRes)], '#4daf4a', linestyle='--', linewidth=4, marker="D", markersize=8, label="Best (40)")
plt.errorbar(x, ionAvgRes, color='#4daf4a', yerr=ionAvgResDev, linestyle="None")

plt.plot(x, fat4AvgRes, '#377eb8', marker="s", markersize=markersize, label="Syn (20)")
plt.plot(x, [res/x1 for x1,res in zip(x, fat4BestRes)], '#377eb8', linestyle='--', linewidth=4, marker="s", markersize=8, label="Best (20)")
plt.errorbar(x, fat4AvgRes, color='#377eb8', yerr=fat4AvgResDev, linestyle="None")


plt.plot(x, fat6AvgRes, '#ff7f00', marker="o", markersize=markersize, label="Syn (45)")
plt.plot(x, [res/x1 for x1,res in zip(x, fat6BestRes)], '#ff7f00', linestyle='--', linewidth=4, marker="o", markersize=8, label="Best (45)")
plt.errorbar(x, fat6AvgRes, color='#ff7f00', yerr=fat6AvgResDev, linestyle="None")


plt.legend(loc='upper right', mode="expand", ncol=3, frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Average endpoint resilience', fontsize=20)

plt.grid()
plt.savefig('ospfAvgRes.eps',  format='eps', dpi=1000, bbox_inches='tight')
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


