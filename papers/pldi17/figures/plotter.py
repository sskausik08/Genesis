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

plt.plot(x, ionOspfTime, '#ff7f00', marker="o", label="Best (Ion)")
plt.errorbar(x, ionOspfTime, color='#ff7f00', yerr=ionOspfTimeDev, linestyle="None")
plt.plot(x, ionOspfTimeWorst, '#377eb8',marker="^", label="Worst (Ion)")
plt.errorbar(x, ionOspfTimeWorst, color='#377eb8', yerr=ionOspfTimeWorstDev, linestyle="None")

plt.plot(x, fatOspfTime, '#4daf4a',marker="D", label="Best (Fat-8)")
plt.errorbar(x, fatOspfTime, color='#4daf4a', yerr=fatOspfTimeDev, linestyle="None")
plt.plot(x, fatOspfTimeWorst, '#984ea3', marker="s", label="Worst (Fat-8)")
plt.errorbar(x, fatOspfTimeWorst, color='#984ea3', yerr=fatOspfTimeWorstDev, linestyle="None")

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

markersize = 11

plt.xlim(xmin=190, xmax=1010)

plt.plot(x, ionConf, '#ff7f00', marker="o", label="Best (Ion)")
plt.errorbar(x, ionConf, color='#ff7f00', yerr=ionConfDev, linestyle="None")
plt.plot(x, ionConfWorst, '#377eb8',marker="^", label="Worst (Ion)")
plt.errorbar(x, ionConfWorst, color='#377eb8', yerr=ionConfWorstDev, linestyle="None")

plt.plot(x, fatConf, '#4daf4a',marker="D", label="Best (Fat-8)")
plt.errorbar(x, fatConf, color='#4daf4a', yerr=fatConfDev, linestyle="None")
plt.plot(x, fatConfWorst, '#984ea3', marker="s", label="Worst (Fat-8)")
plt.errorbar(x, fatConfWorst, color='#984ea3', yerr=fatConfWorstDev, linestyle="None")

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
markersize = 11

plt.xlim(xmin=190, xmax=1010)

plt.plot(x, ionTRL, '#4daf4a',marker="D", label="Best (Ion)")
plt.errorbar(x, ionTRL, color='#4daf4a', yerr=ionTRLDev, linestyle="None")
plt.plot(x, ionTRLWorst, '#377eb8',marker="^", label="Worst (Ion)")
plt.errorbar(x, ionTRLWorst, color='#377eb8', yerr=ionTRLWorstDev, linestyle="None")

plt.plot(x, fatTRL, '#ff7f00', marker="o", label="Best (Fat-8)")
plt.errorbar(x, fatTRL, color='#ff7f00', yerr=fatTRLDev, linestyle="None")
plt.plot(x, fatTRLWorst, '#984ea3', marker="s", label="Worst (Fat-8)")
plt.errorbar(x, fatTRLWorst, color='#984ea3', yerr=fatTRLWorstDev, linestyle="None")

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

plt.plot(x, ionTRL, '#4daf4a',marker="D", label="TRL Ratio (Ion)")
plt.errorbar(x, ionTRL, color='#4daf4a', yerr=ionTRLDev, linestyle="None")
plt.plot(x, ionConf, '#377eb8',marker="^", label="Conf Ratio (Ion)")
plt.errorbar(x, ionConf, color='#377eb8', yerr=ionConfDev, linestyle="None")

plt.plot(x, fatTRL, '#ff7f00', marker="o", label="TRL Ratio  (Fat-8)")
plt.errorbar(x, fatTRL, color='#ff7f00', yerr=fatTRLDev, linestyle="None")
plt.plot(x, fatConf, '#984ea3', marker="s", label="Conf Ratio (Fat-8)")
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

fatTime =  [0.04263912741,0.3389375772,2.070554649,4.668311028,7.679610742,10.82252409,12.59832289,20]
fatTimeDev = [0.02472738843,0.1789896801,1.013203957,0.9042154791,1.170098253,0.9448482264,1.129939945,2]

plt.xlim(xmin=15, xmax=210)

plt.plot(x, ionTime, '#4daf4a',marker="D", label="Time Ratio (Colt)")
plt.errorbar(x, ionTime, yerr=ionTimeDev, linestyle="None")

plt.plot(x, fatTime, '#ff7f00', marker="o", label="Time Ratio  (Fat-6)")
plt.errorbar(x, fatTime, yerr=fatTimeDev, linestyle="None")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Number of Paths', fontsize=20)
plt.ylabel('Average time per path', fontsize=20)

plt.grid()
plt.savefig('ospfTime.eps', format='eps', dpi=1000, bbox_inches='tight')

# mcmc = plt.figure(2)
# f = open("zep-mcmc.csv")
# x = []
# y = []
# for line in f:
#     fields = line.split("\t")
#     x.append(int(fields[0]))
#     y.append(float(fields[1]))

# plt.plot(x, y, '#ff7f00', marker="o")

# plt.xlabel('Iteration')
# plt.ylabel('MCMC Score')

# plt.grid()
# plt.savefig('mcmc.png', format='png', dpi=300, bbox_inches='tight')


