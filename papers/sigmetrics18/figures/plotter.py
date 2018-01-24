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
from matplotlib import legend_handler
from matplotlib.lines import Line2D

matplotlib.rcParams['text.usetex'] = True
label_size = 12
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

label_size = 17
matplotlib.rcParams['xtick.labelsize'] = label_size 
matplotlib.rcParams['ytick.labelsize'] = label_size 

mcmcFig, (ax1) = plt.subplots(1, 1, figsize=(5, 4.5))

x = range(200, 1200, 200)
fatBGP = [0.5374582832,0.6363530327,0.6772793902,0.6926588771,0.7191581698]
fatBGPDev = [0.108141025,0.06570855045,0.07627663603,0.06172817589,0.07534140738]

fatSR = [1.657828742,1.01794802,0.8033826657,0.6954567232,0.6683307083]
fatSRDev = [0.6925780782,0.2658573956,0.2039409816,0.1406134489,0.09359728377]

fatRes = [0.9651012484,0.9968658583,1.05642215,1.075417458,1.105757245]
fatResDev = [0.04498975121,0.04621815565,0.0805032214,0.06748772542,0.06435999191]

ax1.set_xlim([190, 1010])
ax1.set_ylim([0,2])

ax1.plot(x, fatBGP, '#377eb8',marker="D", markersize=markersize, label="BGP")
ax1.errorbar(x, fatBGP, color='#377eb8', yerr=fatBGPDev, linestyle="None")

ax1.plot(x, fatSR, '#ff7f00', marker="o", markersize=markersize, label="SR")
ax1.errorbar(x, fatSR, color='#ff7f00', yerr=fatSRDev, linestyle="None")

ax1.plot(x, fatRes, '#984ea3', marker="s", markersize=markersize, label="Resil.")
ax1.errorbar(x, fatRes, color='#984ea3', yerr=fatResDev, linestyle="None")

ax1.legend(loc='upper right', ncol=3, frameon=False, fontsize=14)

ax1.set_xlabel('\#Paths', fontsize=16)
ax1.set_ylabel('Ratio', fontsize=16)

ax1.grid()
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
label_size = 20
matplotlib.rcParams['xtick.labelsize'] = label_size 
matplotlib.rcParams['ytick.labelsize'] = label_size 

ospfWaypointFig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
adjustFigAspect(ospfWaypointFig, 2.5)
x = range(10, 90, 10)
xticks = range(10, 90, 20)
yticks = [0, 1, 10, 100, 1000]
zeroes = [1 for a in range(8)]
genesisTime = [1.905232944, 4.054856551, 6.447951472, 8.774414492, 11.60772855, 14.57009258,18.05601811, 21.1040017]
totTime = [2.650796689,5.545891339,15.29532384,31.4204547,97.32999361,209.9557621,338.6178232,437.1733794]
#totTime = [a + b for a,b in zip(genesisTime,zeppelinTime)]

ax1.set_xlim([10, 80])
ax1.set_xticks(xticks)
ax1.set_ylim([0, 1000])

ax1.plot(x, genesisTime, '#d95f02')
ax1.plot(x, totTime, '#7570b3')

ax1.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
ax1.fill_between(x, 0, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")
ax1.legend(loc='upper left')

#plt.legend(loc='best', frameon=False, fontsize=18)
ax1.set_ylabel('Time (s)', fontsize=20)
ax1.set_xlabel('\#Paths \n (a) \#Sets: 2', fontsize=20)

ax1.grid()

genesisTime = [1.898177683,4.137906945,6.411716133,8.66710724,11.57976503,14.78331525,17.91517298,21.24656556]
totTime = [3.339358291,8.092288089,30.90892007,101.4620721,284.8738477,531.9663218,743.310784,923.8451524]

ax2.set_xlim([10, 80])
ax2.set_xticks(xticks)
ax2.set_ylim([0, 1000])

ax2.plot(x, genesisTime, '#d95f02')
ax2.plot(x, totTime, '#7570b3',)

z = ax2.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
g = ax2.fill_between(x, 0, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax2.set_xlabel('\#Paths \n (b) \#Sets: 5', fontsize=20)
ax2.grid()

plt.legend(['Genesis','Zeppelin'], fontsize=20,  ncol=2, loc='upper center', 
    bbox_to_anchor=[-0.095, 1.50], columnspacing=1.0, labelspacing=0.0,handletextpad=0.0, 
    handlelength=1.5, fancybox=True)

leg = plt.gca().get_legend()
# ltext  = leg.get_texts()  # all the text.Text instance in the legend
llines = leg.get_lines()  # all the lines.Line2D instance in the legend
# frame  = leg.get_frame()  # the patch.Rectangle instance surrounding the legend

# see text.Text, lines.Line2D, and patches.Rectangle for more info on
# the settable properties of lines, text, and rectangles
# frame.set_facecolor('0.80')      # set the frame face color to light gray
# plt.setp(ltext, fontsize='small')    # the legend text fontsize
plt.setp(llines, linewidth=7)      # the legend linewidth
#leg.draw_frame(False)           # don't draw the legend frame
plt.savefig('ospfwaypoint.eps', format='eps', dpi=1000, bbox_inches='tight')

#############################################################################

ospfWaypointFig2, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
adjustFigAspect(ospfWaypointFig2, 2.5)
x = range(10, 60, 10)
genesisTime = [13.22395077,  24.42584836, 97.5888415,  216.4309352, 661.514916]
zepTime = [58.84612486, 237.091137,  477.554593,  864.4207624, 1270.605623]
totTime = [a + b for a,b in zip(genesisTime,zepTime)]

ax1.set_xlim([10, 50])
ax1.set_xticks(x)
ax1.set_ylim([0, 2000])

ax1.plot(x, genesisTime, '#d95f02')
ax1.plot(x, totTime, '#7570b3',)

ax1.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
ax1.fill_between(x, 0, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax1.set_ylabel('Time (s)', fontsize=20)
ax1.set_xlabel('\#Paths \n (a) \#Sets: 2', fontsize=20)

ax1.grid()

x = range(10, 50, 10)

genesisTime = [10.657,26.624,70.97,214.161]
zepTime = [122.16,430.03,905.98,1642.731939]
totTime = [a + b for a,b in zip(genesisTime,zepTime)]

ax2.set_xlim([10, 40])
ax2.set_xticks(x)
ax2.set_ylim([0, 2000])


ax2.plot(x, genesisTime, '#d95f02')
ax2.plot(x, totTime, '#7570b3',)

z = ax2.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
g = ax2.fill_between(x, 0, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax2.set_xlabel('\#Paths \n (b) \#Sets: 5', fontsize=20)
ax2.grid()


plt.legend(['Genesis','Zeppelin'], fontsize=20,  ncol=2, loc='upper center', 
    bbox_to_anchor=[-0.095, 1.50], columnspacing=1.0, labelspacing=0.0,handletextpad=0.0, 
    handlelength=1.5, fancybox=True)

leg = plt.gca().get_legend()
# ltext  = leg.get_texts()  # all the text.Text instance in the legend
llines = leg.get_lines()  # all the lines.Line2D instance in the legend
# frame  = leg.get_frame()  # the patch.Rectangle instance surrounding the legend

# see text.Text, lines.Line2D, and patches.Rectangle for more info on
# the settable properties of lines, text, and rectangles
# frame.set_facecolor('0.80')      # set the frame face color to light gray
# plt.setp(ltext, fontsize='small')    # the legend text fontsize
plt.setp(llines, linewidth=7)      # the legend linewidth
#leg.draw_frame(False)           # don't draw the legend frame
plt.savefig('ospfwaypoint2.eps', format='eps', dpi=1000, bbox_inches='tight')


#################################################################

ospfIsolationFig, (ax1, ax2) = plt.subplots(1, 2, sharey=True)
adjustFigAspect(ospfIsolationFig, 2.5)

x = range(20, 90, 10)
xticks = range(20, 90, 20)
zeroes = [1 for a in range(7)]
genesisTime = [2.66, 4.31, 5.7, 7.36, 8.3, 9.5, 10.95]
totTime = [2.98, 5.59, 9.62, 13.45, 22.89, 33.98, 62.37 ]

ax1.set_xlim([20, 80])
ax1.set_xticks(xticks)
ax1.set_ylim([0, 80])
yticks = range(20, 100, 20)
ax1.set_yticks(yticks)

ax1.plot(x, genesisTime, '#d95f02')
ax1.plot(x, totTime, '#7570b3',)

ax1.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
ax1.fill_between(x, zeroes, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax1.set_ylabel('Time (s)', fontsize=20)
ax1.set_xlabel('\#Paths \n (a) Reachability', fontsize=20)
ax1.grid()
x = range(20, 100, 20)
genesisTime = [2.81, 12.94, 32.15, 217.46 ]
totTime = [3.34, 35.99, 141.25, 507.36 ]
zeroes = [1 for a in range(4)]

ax2.set_xlim([20, 80])
ax2.set_xticks(x)
ax2.set_ylim([0, 500])
yticks = range(0, 600, 100)
ax1.set_yticks(yticks)

ax2.plot(x, genesisTime, '#d95f02')
ax2.plot(x, totTime, '#7570b3',)

z = ax2.fill_between(x, genesisTime, totTime, color='#7570b3', alpha='0.5', label="Zeppelin")
g = ax2.fill_between(x, zeroes, genesisTime, color='#d95f02', alpha='0.5', label="Genesis")

#plt.legend(loc='best', frameon=False, fontsize=18)
ax2.set_xlabel('\#Paths \n (b) Isolation', fontsize=20)
ax2.grid()
plt.legend(['Genesis','Zeppelin'], fontsize=20,  ncol=2, loc='upper center', 
    bbox_to_anchor=[-0.095, 1.50], columnspacing=1.0, labelspacing=0.0,handletextpad=0.0, 
    handlelength=1.5, fancybox=True)

leg = plt.gca().get_legend()
# ltext  = leg.get_texts()  # all the text.Text instance in the legend
llines = leg.get_lines()  # all the lines.Line2D instance in the legend
# frame  = leg.get_frame()  # the patch.Rectangle instance surrounding the legend

# see text.Text, lines.Line2D, and patches.Rectangle for more info on
# the settable properties of lines, text, and rectangles
# frame.set_facecolor('0.80')      # set the frame face color to light gray
# plt.setp(ltext, fontsize='small')    # the legend text fontsize
plt.setp(llines, linewidth=7)      # the legend linewidth
#leg.draw_frame(False)           # don't draw the legend frame
plt.savefig('ospfisolation.eps', format='eps', dpi=1000, bbox_inches='tight')

###########################################################
label_size = 20
matplotlib.rcParams['xtick.labelsize'] = label_size 
matplotlib.rcParams['ytick.labelsize'] = label_size 

zepres10W = [0.5566037736,0.8015873016,0.674796748,0.7863247863,0.6732673267,0.6725663717,0.55,0.7234042553,0.7555555556,0.7065217391,0.7777777778,0.7169811321,0.5894736842,0.8172043011,0.7232142857,0.6451612903,0.7272727273,0.7976190476,0.698630137,0.75,0.6805555556,0.5882352941,0.7333333333,0.7040816327,0.8072289157,0.7532467532,0.7340425532,0.6868686869,0.5842696629,0.6082474227,0.84,0.8035714286,0.7413793103,0.6344086022,0.6326530612,0.7582417582,0.4719101124,0.7431192661,0.6989247312,0.6666666667,0.7386363636,0.6129032258,0.7642276423,0.6632653061,0.5979381443,0.6829268293,0.8021978022,0.5806451613,0.7157894737,0.7222222222,0.7808219178,0.7325581395,0.900990099,0.7608695652,0.5596330275,0.72,0.7978723404,0.6404494382,0.6226415094,0.6460176991,0.5494505495,0.618556701,0.6136363636,0.725,0.6043956044,0.7848101266,0.6842105263,0.6575342466,0.7553191489,0.5326086957,0.6442307692,0.7391304348,0.7472527473,0.6458333333,0.8796296296,0.7157894737,0.8590604027,0.7070707071,0.7222222222,0.7884615385,0.6460176991,0.8130841122,0.8148148148,0.7394957983,0.6857142857,0.7333333333,0.6571428571,0.6111111111,0.6666666667,0.7974683544,0.8275862069,0.7361111111,0.7162162162]
zepres10WR = [0.9405405405,0.9453551913,0.9402173913,0.994047619,0.995,0.9704433498,0.9684210526,0.955,0.9757281553,0.9659090909,0.9590643275,0.9494382022,0.9888268156,0.9554140127,0.9701492537,0.9754901961,0.9329608939,0.968503937,0.9880239521,0.976744186,0.9942196532,0.9888268156,0.9677419355,0.9900497512,0.9870967742,0.9943181818,0.9404761905,0.975,0.9805194805,1,1,0.9903846154,0.9816513761,0.9841269841,0.9623655914,0.9730941704,0.9849246231,0.9734042553,0.9923664122,0.9885057471,1,0.9666666667,0.963190184,0.9949238579,0.9907834101,1,0.9651162791,0.9902912621,1,0.9950980392,0.9870967742,0.9432624113,0.9900497512,1,0.9896373057,0.98,0.9698795181,0.9834254144,0.9770114943,0.9777777778,1,0.995412844,0.9937106918,0.9943181818,0.9700598802,0.9936708861,0.9431818182,0.9929078014,0.9585798817,0.9349112426,0.9943502825,0.9790575916,0.9130434783,0.9277108434,1,0.9378531073,0.9510869565,1,0.981981982,0.9824561404,0.9777777778,0.979020979,0.9878787879,0.99375,0.9622641509,0.9805194805,0.9842105263,0.9795918367,0.9951690821,1,0.9824561404,0.9795918367,0.9756097561]
zepres10P = [0.3409090909, 0.4285714286, 0.3854166667, 0.4777777778, 0.5102040816, 0.5319148936, 0.402173913, 0.6020408163, 0.5625, 0.4772727273, 0.5, 0.4642857143, 0.4756097561, 0.4418604651, 0.4545454545, 0.2727272727, 0.3510638298, 0.3372093023, 0.5138888889, 0.5, 0.5675675676, 0.5540540541, 0.4459459459, 0.4222222222, 0.4625, 0.421686747, 0.5494505495, 0.3595505618, 0.5368421053, 0.4395604396, 0.5, 0.5465116279, 0.5833333333, 0.3111111111, 0.4886363636, 0.4117647059, 0.3614457831, 0.5348837209, 0.4186046512, 0.4487179487, 0.4756097561, 0.4588235294, 0.3950617284, 0.525, 0.3409090909, 0.3875, 0.5714285714, 0.512195122, 0.4137931034, 0.5053763441, 0.5476190476, 0.5217391304, 0.5913978495, 0.4946236559, 0.4352941176, 0.5161290323, 0.5308641975, 0.4137931034, 0.3908045977, 0.4777777778, 0.4615384615, 0.4831460674, 0.3707865169, 0.5697674419, 0.3793103448, 0.4943820225, 0.5934065934, 0.4946236559, 0.4880952381, 0.3375, 0.4555555556, 0.575, 0.575, 0.358974359, 0.4943820225, 0.575, 0.5119047619, 0.5, 0.4712643678, 0.4819277108, 0.4705882353, 0.4941176471, 0.5, 0.4512195122, 0.4523809524, 0.5319148936, 0.5308641975, 0.3647058824, 0.4683544304, 0.6075949367, 0.5189873418, 0.5308641975, 0.6233766234]

ospfResilienceFig, (ax1, ax2, ax3) = plt.subplots(1, 3, sharey=True, figsize=(6.86,2))
ospfResilienceFig.subplots_adjust(left=0.1)
#adjustFigAspect(ospfResilienceFig, 3)


ax1.set_xlim([0, 1])
ax1.set_ylim([0, 1])
ax1.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax1.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax1.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax1.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax1.scatter(zepres10W, zepres10WR, marker="x", s=20, color='#ff7f00')
ax1.plot([0.0, 1.0], linestyle='--', color="black") 
ax1.set_xlabel('1-WC Score \n \#Policies:10', fontsize=13)
ax1.set_ylabel('2-WC Score', fontsize=13)
ax1.grid()

#ax1.scatter(zepres10P, zepres10WR, marker="^", s=3, color='#377eb8')


zepres20W=[0.5212765957, 0.5837563452, 0.5555555556, 0.6585365854, 0.5531914894, 0.5476190476, 0.6458333333, 0.7384615385, 0.7, 0.8092105263, 0.5437788018, 0.4945054945, 0.64, 0.6050955414, 0.6448087432, 0.5806451613, 0.6826923077, 0.6397515528, 0.6944444444, 0.6568047337, 0.6779661017, 0.5705521472, 0.7041420118, 0.5663265306, 0.643902439, 0.5898876404, 0.6585365854, 0.5588235294, 0.5873015873, 0.5833333333, 0.6833333333, 0.6285714286, 0.6363636364, 0.5384615385, 0.6318681319, 0.6560509554, 0.7806451613, 0.6226415094, 0.6627218935, 0.5953757225, 0.6440677966, 0.6607142857, 0.6097560976, 0.6741573034, 0.717791411, 0.6467391304, 0.5454545455, 0.5609756098, 0.4785276074, 0.625, 0.6075268817, 0.6217948718, 0.7362637363, 0.7102272727, 0.5591397849, 0.5838509317, 0.582010582, 0.5857988166, 0.6467391304, 0.6790123457, 0.6073619632, 0.6448087432, 0.5744680851, 0.6559139785, 0.6761363636, 0.6337209302, 0.6793478261, 0.6228571429, 0.608490566, 0.6432160804, 0.6448087432, 0.6258064516, 0.6917808219, 0.6868686869, 0.5783783784, 0.5028571429, 0.6193548387, 0.597826087, 0.619047619, 0.6751592357, 0.7142857143, 0.6098654709, 0.6358695652, 0.6496815287, 0.6723163842, 0.6447368421, 0.6686046512, 0.6507936508, 0.5555555556, 0.7207792208, 0.6369426752, 0.6804733728, 0.5952380952, 0.625, 0.6451612903, 0.6229508197, 0.6582914573, 0.7745098039, 0.6413043478, 0.6397849462]
zepres20WR=[0.9950617284, 0.9765625, 0.9852941176, 0.9772727273, 0.9794871795, 0.99756691, 1, 0.9975247525, 1, 0.9972752044, 0.9831325301, 0.9975124378, 0.9841688654, 0.9837398374, 0.9945504087, 0.9899749373, 1, 0.9810810811, 0.9948979592, 0.9925187032, 0.9742930591, 0.9825436409, 1, 0.9977678571, 0.9663212435, 0.9976470588, 0.9791666667, 0.9722222222, 0.9976019185, 0.9756097561, 0.9817232376, 0.9867724868, 0.9882352941, 0.9975062344, 0.9954022989, 0.9927536232, 0.9898477157, 1, 0.9976359338, 0.9809976247, 0.9949494949, 0.9873417722, 0.9931034483, 0.986631016, 0.9922879177, 0.9976019185, 1, 0.9766081871, 0.9944751381, 0.9755434783, 0.9580246914, 0.9566473988, 0.9761904762, 0.9977375566, 0.9613402062, 0.9737609329, 1, 0.9850746269, 0.9738219895, 0.9796954315, 0.9895287958, 0.9920634921, 0.9932126697, 0.9571428571, 0.9950980392, 0.9921465969, 0.9869791667, 0.9693593315, 0.9823677582, 0.9884526559, 0.9927710843, 0.9895561358, 0.9867021277, 1, 0.9743589744, 0.9908466819, 0.9975903614, 0.9803439803, 0.9956616052, 1, 0.9873096447, 1, 0.9933628319, 0.9779614325, 0.9753424658, 0.9607250755, 0.9902676399, 0.9946949602, 0.9925373134, 0.9809069212, 0.9839572193, 0.9831460674, 0.9974160207, 0.9973404255, 0.9867724868, 0.9792746114, 0.9844444444, 0.9880095923, 0.9975961538, 0.9928571429]
zepres20P=[0.3988095238,0.4293785311,0.4736842105,0.5277777778,0.5229885057,0.4588235294,0.4698795181,0.4111111111,0.5182926829,0.450617284,0.3825136612,0.4683544304,0.4810126582,0.4519774011,0.497005988,0.4678362573,0.3631284916,0.549132948,0.4685714286,0.5085714286,0.4689265537,0.4733727811,0.4858757062,0.4545454545,0.4254143646,0.4535519126,0.4411764706,0.4666666667,0.4093567251,0.4831460674,0.5348837209,0.476744186,0.417721519,0.4111111111,0.4352941176,0.5,0.5714285714,0.4085365854,0.462962963,0.4393063584,0.5263157895,0.52,0.3988439306,0.4337349398,0.5117647059,0.3875,0.4367816092,0.4319526627,0.4394904459,0.4792899408,0.5088757396,0.493902439,0.5085714286,0.4910179641,0.5163043478,0.5090909091,0.4674556213,0.4702702703,0.4430379747,0.5120481928,0.4534883721,0.4647058824,0.402173913,0.4096385542,0.4478527607,0.5029239766,0.530726257,0.4262295082,0.4385964912,0.3865030675,0.4413407821,0.5975609756,0.5197740113,0.4198895028,0.5191256831,0.3771428571,0.4649681529,0.4795321637,0.4864864865,0.5182926829,0.5316455696,0.591954023,0.4968553459,0.4777070064,0.5114942529,0.5352941176,0.5212121212,0.5254237288,0.5153374233,0.5029585799,0.4727272727,0.4465408805,0.502994012,0.4240506329,0.4825581395,0.4034090909,0.5406976744,0.4858757062,0.4457142857,0.4113924051,0.4748603352,0.4267515924,0.5,0.5,0.4423076923,0.4125,0.4682080925,0.4237288136,0.4606060606,0.4596273292,0.5086705202,0.4748603352,0.4157303371,0.4615384615,0.4367816092,0.4938271605,0.50625,0.4318181818]
zepres20P=zepres20P[:100]

ax2.set_xlim([0, 1])
ax2.set_ylim([0, 1])
ax2.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax2.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax2.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax2.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax2.scatter(zepres20W, zepres20WR, marker="x", s=20, color='#ff7f00')
ax2.plot([0.0, 1.0], linestyle='--', color="black") 
ax2.set_xlabel('1-WC Score \n \#Policies:20', fontsize=13)
# ax2.set_ylabel('2-WC Score', fontsize=13)
ax2.grid()
#ax2.scatter(zepres20P, zepres20WR, marker="^", s=3, color='#377eb8')

zepres40WR=[0.9899371069, 0.9872611465, 0.9741267788, 0.9907529723, 0.9930795848, 0.9952437574, 0.9917257683, 0.9649350649, 0.98482933, 0.9925925926, 0.9919463087, 0.9874686717, 0.9684210526, 0.9737827715, 0.9836888331, 0.9964705882, 0.9868263473, 0.9930232558, 0.9940828402, 0.9879518072, 0.9951632406, 0.9880810489, 0.9863013699, 0.9950372208, 0.9865196078, 0.992, 0.9912280702, 0.9819277108, 0.9812265332, 0.9858793325, 0.9915865385, 0.9879372738, 0.9976662777, 0.9904648391, 0.9828220859, 0.9894117647, 0.9891696751, 0.9875621891, 0.9920634921, 0.9938499385, 0.9917647059, 0.9900744417, 0.9938423645, 0.985645933, 0.9960988296, 1, 0.9941245593, 0.9863523573, 0.9869976359, 0.9964370546, 1, 0.9829890644, 0.9965831435, 0.9963985594, 0.990521327, 0.9906651109, 0.9796437659, 0.989010989, 0.9889840881, 0.9926108374, 0.994266055, 0.9950372208, 0.9876695438, 0.9915560917, 0.9814600232, 0.9864698647, 0.9952550415, 0.9949302915, 0.9751131222, 0.9966555184, 0.979301423, 0.9906103286, 0.9899623588, 0.9671302149, 0.9853836784, 0.9964705882, 0.9941314554, 0.9908779932, 0.9943310658, 0.9926199262, 0.9821428571, 1, 0.9900497512, 0.9844868735, 0.9905771496, 0.984375, 0.9987669544, 0.9924433249, 0.9929988331, 0.9901531729, 0.9904988124, 0.9951807229, 0.990521327, 0.987819732, 0.9809976247, 0.9899497487, 0.9822109276, 0.9920318725, 0.9909677419, 0.9928143713, 0.9877149877, 0.9902080783, 0.9910025707, 0.9728729963, 0.984, 0.9988023952, 0.9891041162, 1, 0.9806451613, 0.9787798408, 0.9860759494, 0.9896907216, 0.9927623643, 0.9872286079, 0.995, 0.9781553398, 0.9976162098, 0.9963768116]
zepres40WR=zepres40WR[:100]
zepres40W=[0.5705882353,0.567039106,0.572237960,0.623076923,0.529745042,0.505376344,0.581717451,0.571428571,0.53459119,0.604046242,0.638157894,0.59322033,0.548746518,0.532981530,0.558912386,0.544474393,0.546666666,0.508241758,0.589235127,0.54603174,0.617283950,0.55029585,0.646723646,0.639344262,0.607407407,0.535294117,0.649874055,0.588068181,0.603217158,0.564705882,0.498652291,0.57559681,0.536443148,0.616621983,0.56657223,0.513888888,0.52835820,0.55029585,0.515337423,0.541538461,0.595307917,0.584958217,0.538922155,0.518633540,0.553623188,0.546012269,0.540540540,0.555555555,0.563685636,0.593659942,0.5389408,0.538904891,0.492021276,0.547058823,0.586402266,0.513297872,0.628169014,0.568047337,0.601648351,0.585760517,0.612359550,0.536656891,0.525679758,0.52,0.56651567,0.481792717,0.533141210,0.569105691,0.51562,0.458115832,0.508620689,0.534435261,0.61562,0.494350825,0.563888888,0.571428571,0.543604651,0.546511627,0.,0.559340659,0.545180722,0.561959654,0.543103448,0.531446540,0.611764705,0.558333333,0.557746478,0.542772861,0.56037151,0.545961002,0.517857142,0.585889570,0.575418994,0.604712041,0.551319648,0.566878980,0.455307262,0.542028985,0.565749235,0.520215633,0.586592178,0.577039274,0.546546546,0.623306233,0.521739130,0.528925619,0.548286604,0.56639566,0.560773480,0.576802507, 0.510086455,0.530898876,0.513761467,0.521472392,0.572580645,0.477611940,0.484240687,0.557522123]
zepres40W=zepres40W[:100]
zepres40P=[0.4498480243, 0.4498480243, 0.4297994269, 0.4281524927, 0.4501424501, 0.4237288136, 0.4664804469, 0.3880597015, 0.4409937888, 0.4756097561, 0.45625, 0.4941520468, 0.43454039, 0.4766081871, 0.4585798817, 0.4542772861, 0.4154727794, 0.4188034188, 0.4464285714, 0.4233128834, 0.4739884393, 0.5129682997, 0.4689265537, 0.4210526316, 0.4561403509, 0.4479768786, 0.4928774929, 0.447592068, 0.4289940828, 0.4474474474, 0.4223433243, 0.5070028011, 0.4285714286, 0.4540229885, 0.4110787172, 0.3879310345, 0.4389534884, 0.4386503067, 0.4046242775, 0.4520958084, 0.4537037037, 0.5226586103, 0.4714714715, 0.4660493827, 0.4319526627, 0.4542682927, 0.4425770308, 0.4492753623, 0.5190615836, 0.5014749263, 0.4078549849, 0.4485714286, 0.4457142857, 0.4248554913, 0.431547619, 0.4683908046, 0.4847560976, 0.4545454545, 0.4510385757, 0.4868804665, 0.4632768362, 0.4678362573, 0.4302670623, 0.4924012158, 0.4384384384, 0.4159021407, 0.4253521127, 0.4383954155, 0.4198895028, 0.4309392265, 0.406779661, 0.4808259587, 0.4565826331, 0.438547486, 0.4248554913, 0.4653179191, 0.474137931, 0.4733727811, 0.4134078212, 0.4763313609, 0.4255319149, 0.4599406528, 0.4461538462, 0.4298245614, 0.4337349398, 0.4314285714, 0.4351851852, 0.4427710843, 0.4823529412, 0.4578651685, 0.4135977337, 0.5, 0.5027624309, 0.5, 0.4656716418, 0.4492753623, 0.4293948127, 0.4561933535, 0.4391691395, 0.3767705382, 0.447761194, 0.4507462687, 0.4135802469, 0.4461538462, 0.4513274336, 0.452173913, 0.4740061162, 0.5102040816, 0.4272727273, 0.4277108434, 0.4651810585, 0.4127906977, 0.4311377246, 0.4480712166, 0.4434782609, 0.3994252874, 0.4245014245, 0.4786324786]
zepres40P=zepres40P[:100]

ax3.set_xlim([0, 1])
ax3.set_ylim([0, 1])
ax3.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax3.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax3.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax3.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax3.scatter(zepres40W, zepres40WR, marker="x", s=20, color='#ff7f00')
ax3.plot([0.0, 1.0], linestyle='--', color="black") 
ax3.set_xlabel('1-WC Score \n \#Policies:40', fontsize=13)
# ax3.set_ylabel('2-WC Score', fontsize=13)
ax3.grid()

plt.savefig('ospfresilience.eps', format='eps', dpi=1000, bbox_inches='tight')

ospfResilienceFig2, (ax1, ax2, ax3) = plt.subplots(1, 3, sharey=True, figsize=(6.86,2))

ax1.set_xlim([0, 1])
ax1.set_ylim([0, 1])
ax1.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax1.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax1.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax1.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax1.scatter(zepres10P, zepres10WR, marker="x", s=20, color='#377eb8')
ax1.plot([0.0, 1.0], linestyle='--', color="black") 
ax1.set_xlabel('PC Score \n \#Policies:10', fontsize=13)
ax1.set_ylabel('2-WC Score', fontsize=13)
ax1.grid()

#ax1.scatter(zepres10P, zepres10WR, marker="^", s=3, color='#377eb8')


zepres20W=[0.5212765957, 0.5837563452, 0.5555555556, 0.6585365854, 0.5531914894, 0.5476190476, 0.6458333333, 0.7384615385, 0.7, 0.8092105263, 0.5437788018, 0.4945054945, 0.64, 0.6050955414, 0.6448087432, 0.5806451613, 0.6826923077, 0.6397515528, 0.6944444444, 0.6568047337, 0.6779661017, 0.5705521472, 0.7041420118, 0.5663265306, 0.643902439, 0.5898876404, 0.6585365854, 0.5588235294, 0.5873015873, 0.5833333333, 0.6833333333, 0.6285714286, 0.6363636364, 0.5384615385, 0.6318681319, 0.6560509554, 0.7806451613, 0.6226415094, 0.6627218935, 0.5953757225, 0.6440677966, 0.6607142857, 0.6097560976, 0.6741573034, 0.717791411, 0.6467391304, 0.5454545455, 0.5609756098, 0.4785276074, 0.625, 0.6075268817, 0.6217948718, 0.7362637363, 0.7102272727, 0.5591397849, 0.5838509317, 0.582010582, 0.5857988166, 0.6467391304, 0.6790123457, 0.6073619632, 0.6448087432, 0.5744680851, 0.6559139785, 0.6761363636, 0.6337209302, 0.6793478261, 0.6228571429, 0.608490566, 0.6432160804, 0.6448087432, 0.6258064516, 0.6917808219, 0.6868686869, 0.5783783784, 0.5028571429, 0.6193548387, 0.597826087, 0.619047619, 0.6751592357, 0.7142857143, 0.6098654709, 0.6358695652, 0.6496815287, 0.6723163842, 0.6447368421, 0.6686046512, 0.6507936508, 0.5555555556, 0.7207792208, 0.6369426752, 0.6804733728, 0.5952380952, 0.625, 0.6451612903, 0.6229508197, 0.6582914573, 0.7745098039, 0.6413043478, 0.6397849462]
zepres20WR=[0.9950617284, 0.9765625, 0.9852941176, 0.9772727273, 0.9794871795, 0.99756691, 1, 0.9975247525, 1, 0.9972752044, 0.9831325301, 0.9975124378, 0.9841688654, 0.9837398374, 0.9945504087, 0.9899749373, 1, 0.9810810811, 0.9948979592, 0.9925187032, 0.9742930591, 0.9825436409, 1, 0.9977678571, 0.9663212435, 0.9976470588, 0.9791666667, 0.9722222222, 0.9976019185, 0.9756097561, 0.9817232376, 0.9867724868, 0.9882352941, 0.9975062344, 0.9954022989, 0.9927536232, 0.9898477157, 1, 0.9976359338, 0.9809976247, 0.9949494949, 0.9873417722, 0.9931034483, 0.986631016, 0.9922879177, 0.9976019185, 1, 0.9766081871, 0.9944751381, 0.9755434783, 0.9580246914, 0.9566473988, 0.9761904762, 0.9977375566, 0.9613402062, 0.9737609329, 1, 0.9850746269, 0.9738219895, 0.9796954315, 0.9895287958, 0.9920634921, 0.9932126697, 0.9571428571, 0.9950980392, 0.9921465969, 0.9869791667, 0.9693593315, 0.9823677582, 0.9884526559, 0.9927710843, 0.9895561358, 0.9867021277, 1, 0.9743589744, 0.9908466819, 0.9975903614, 0.9803439803, 0.9956616052, 1, 0.9873096447, 1, 0.9933628319, 0.9779614325, 0.9753424658, 0.9607250755, 0.9902676399, 0.9946949602, 0.9925373134, 0.9809069212, 0.9839572193, 0.9831460674, 0.9974160207, 0.9973404255, 0.9867724868, 0.9792746114, 0.9844444444, 0.9880095923, 0.9975961538, 0.9928571429]
zepres20P=[0.3988095238,0.4293785311,0.4736842105,0.5277777778,0.5229885057,0.4588235294,0.4698795181,0.4111111111,0.5182926829,0.450617284,0.3825136612,0.4683544304,0.4810126582,0.4519774011,0.497005988,0.4678362573,0.3631284916,0.549132948,0.4685714286,0.5085714286,0.4689265537,0.4733727811,0.4858757062,0.4545454545,0.4254143646,0.4535519126,0.4411764706,0.4666666667,0.4093567251,0.4831460674,0.5348837209,0.476744186,0.417721519,0.4111111111,0.4352941176,0.5,0.5714285714,0.4085365854,0.462962963,0.4393063584,0.5263157895,0.52,0.3988439306,0.4337349398,0.5117647059,0.3875,0.4367816092,0.4319526627,0.4394904459,0.4792899408,0.5088757396,0.493902439,0.5085714286,0.4910179641,0.5163043478,0.5090909091,0.4674556213,0.4702702703,0.4430379747,0.5120481928,0.4534883721,0.4647058824,0.402173913,0.4096385542,0.4478527607,0.5029239766,0.530726257,0.4262295082,0.4385964912,0.3865030675,0.4413407821,0.5975609756,0.5197740113,0.4198895028,0.5191256831,0.3771428571,0.4649681529,0.4795321637,0.4864864865,0.5182926829,0.5316455696,0.591954023,0.4968553459,0.4777070064,0.5114942529,0.5352941176,0.5212121212,0.5254237288,0.5153374233,0.5029585799,0.4727272727,0.4465408805,0.502994012,0.4240506329,0.4825581395,0.4034090909,0.5406976744,0.4858757062,0.4457142857,0.4113924051,0.4748603352,0.4267515924,0.5,0.5,0.4423076923,0.4125,0.4682080925,0.4237288136,0.4606060606,0.4596273292,0.5086705202,0.4748603352,0.4157303371,0.4615384615,0.4367816092,0.4938271605,0.50625,0.4318181818]
zepres20P=zepres20P[:100]

ax2.set_xlim([0, 1])
ax2.set_ylim([0, 1])
ax2.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax2.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax2.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax2.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax2.scatter(zepres20P, zepres20WR, marker="x", s=20, color='#377eb8')
ax2.plot([0.0, 1.0], linestyle='--', color="black") 
ax2.set_xlabel('PC Score \n \#Policies:20', fontsize=13)
# ax2.set_ylabel('2-WC Score', fontsize=13)
ax2.grid()
#ax2.scatter(zepres20P, zepres20WR, marker="^", s=3, color='#377eb8')

zepres40WR=[0.9899371069, 0.9872611465, 0.9741267788, 0.9907529723, 0.9930795848, 0.9952437574, 0.9917257683, 0.9649350649, 0.98482933, 0.9925925926, 0.9919463087, 0.9874686717, 0.9684210526, 0.9737827715, 0.9836888331, 0.9964705882, 0.9868263473, 0.9930232558, 0.9940828402, 0.9879518072, 0.9951632406, 0.9880810489, 0.9863013699, 0.9950372208, 0.9865196078, 0.992, 0.9912280702, 0.9819277108, 0.9812265332, 0.9858793325, 0.9915865385, 0.9879372738, 0.9976662777, 0.9904648391, 0.9828220859, 0.9894117647, 0.9891696751, 0.9875621891, 0.9920634921, 0.9938499385, 0.9917647059, 0.9900744417, 0.9938423645, 0.985645933, 0.9960988296, 1, 0.9941245593, 0.9863523573, 0.9869976359, 0.9964370546, 1, 0.9829890644, 0.9965831435, 0.9963985594, 0.990521327, 0.9906651109, 0.9796437659, 0.989010989, 0.9889840881, 0.9926108374, 0.994266055, 0.9950372208, 0.9876695438, 0.9915560917, 0.9814600232, 0.9864698647, 0.9952550415, 0.9949302915, 0.9751131222, 0.9966555184, 0.979301423, 0.9906103286, 0.9899623588, 0.9671302149, 0.9853836784, 0.9964705882, 0.9941314554, 0.9908779932, 0.9943310658, 0.9926199262, 0.9821428571, 1, 0.9900497512, 0.9844868735, 0.9905771496, 0.984375, 0.9987669544, 0.9924433249, 0.9929988331, 0.9901531729, 0.9904988124, 0.9951807229, 0.990521327, 0.987819732, 0.9809976247, 0.9899497487, 0.9822109276, 0.9920318725, 0.9909677419, 0.9928143713, 0.9877149877, 0.9902080783, 0.9910025707, 0.9728729963, 0.984, 0.9988023952, 0.9891041162, 1, 0.9806451613, 0.9787798408, 0.9860759494, 0.9896907216, 0.9927623643, 0.9872286079, 0.995, 0.9781553398, 0.9976162098, 0.9963768116]
zepres40WR=zepres40WR[:100]
zepres40W=[0.5705882353,0.567039106,0.572237960,0.623076923,0.529745042,0.505376344,0.581717451,0.571428571,0.53459119,0.604046242,0.638157894,0.59322033,0.548746518,0.532981530,0.558912386,0.544474393,0.546666666,0.508241758,0.589235127,0.54603174,0.617283950,0.55029585,0.646723646,0.639344262,0.607407407,0.535294117,0.649874055,0.588068181,0.603217158,0.564705882,0.498652291,0.57559681,0.536443148,0.616621983,0.56657223,0.513888888,0.52835820,0.55029585,0.515337423,0.541538461,0.595307917,0.584958217,0.538922155,0.518633540,0.553623188,0.546012269,0.540540540,0.555555555,0.563685636,0.593659942,0.5389408,0.538904891,0.492021276,0.547058823,0.586402266,0.513297872,0.628169014,0.568047337,0.601648351,0.585760517,0.612359550,0.536656891,0.525679758,0.52,0.56651567,0.481792717,0.533141210,0.569105691,0.51562,0.458115832,0.508620689,0.534435261,0.61562,0.494350825,0.563888888,0.571428571,0.543604651,0.546511627,0.,0.559340659,0.545180722,0.561959654,0.543103448,0.531446540,0.611764705,0.558333333,0.557746478,0.542772861,0.56037151,0.545961002,0.517857142,0.585889570,0.575418994,0.604712041,0.551319648,0.566878980,0.455307262,0.542028985,0.565749235,0.520215633,0.586592178,0.577039274,0.546546546,0.623306233,0.521739130,0.528925619,0.548286604,0.56639566,0.560773480,0.576802507, 0.510086455,0.530898876,0.513761467,0.521472392,0.572580645,0.477611940,0.484240687,0.557522123]
zepres40W=zepres40W[:100]
zepres40P=[0.4498480243, 0.4498480243, 0.4297994269, 0.4281524927, 0.4501424501, 0.4237288136, 0.4664804469, 0.3880597015, 0.4409937888, 0.4756097561, 0.45625, 0.4941520468, 0.43454039, 0.4766081871, 0.4585798817, 0.4542772861, 0.4154727794, 0.4188034188, 0.4464285714, 0.4233128834, 0.4739884393, 0.5129682997, 0.4689265537, 0.4210526316, 0.4561403509, 0.4479768786, 0.4928774929, 0.447592068, 0.4289940828, 0.4474474474, 0.4223433243, 0.5070028011, 0.4285714286, 0.4540229885, 0.4110787172, 0.3879310345, 0.4389534884, 0.4386503067, 0.4046242775, 0.4520958084, 0.4537037037, 0.5226586103, 0.4714714715, 0.4660493827, 0.4319526627, 0.4542682927, 0.4425770308, 0.4492753623, 0.5190615836, 0.5014749263, 0.4078549849, 0.4485714286, 0.4457142857, 0.4248554913, 0.431547619, 0.4683908046, 0.4847560976, 0.4545454545, 0.4510385757, 0.4868804665, 0.4632768362, 0.4678362573, 0.4302670623, 0.4924012158, 0.4384384384, 0.4159021407, 0.4253521127, 0.4383954155, 0.4198895028, 0.4309392265, 0.406779661, 0.4808259587, 0.4565826331, 0.438547486, 0.4248554913, 0.4653179191, 0.474137931, 0.4733727811, 0.4134078212, 0.4763313609, 0.4255319149, 0.4599406528, 0.4461538462, 0.4298245614, 0.4337349398, 0.4314285714, 0.4351851852, 0.4427710843, 0.4823529412, 0.4578651685, 0.4135977337, 0.5, 0.5027624309, 0.5, 0.4656716418, 0.4492753623, 0.4293948127, 0.4561933535, 0.4391691395, 0.3767705382, 0.447761194, 0.4507462687, 0.4135802469, 0.4461538462, 0.4513274336, 0.452173913, 0.4740061162, 0.5102040816, 0.4272727273, 0.4277108434, 0.4651810585, 0.4127906977, 0.4311377246, 0.4480712166, 0.4434782609, 0.3994252874, 0.4245014245, 0.4786324786]
zepres40P=zepres40P[:100]

ax3.set_xlim([0, 1])
ax3.set_ylim([0, 1])
ax3.set_xticks([0, 0.25, 0.5, 0.75, 1])
ax3.set_xticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])
ax3.set_yticks([0, 0.25, 0.5, 0.75, 1])
ax3.set_yticklabels(["$0$", r"$\frac{1}{4}$", r"$\frac{1}{2}$", r"$\frac{3}{4}$", "$1$"])

ax3.scatter(zepres40P, zepres40WR, marker="x", s=20, color='#377eb8')
ax3.plot([0.0, 1.0], linestyle='--', color="black") 
ax3.set_xlabel('PC Score \n \#Policies:40', fontsize=13)
# ax3.set_ylabel('2-WC Score', fontsize=13)
ax3.grid()

plt.savefig('ospfresilience2.eps', format='eps', dpi=1000, bbox_inches='tight')

ospfBaseline, (ax1) = plt.subplots(1, 1, figsize=(3, 3))
# zepConRes=[0.9523809524,1,1,1,1,0.9523809524,1,1,0.8695652174,1,1,1,1,0.9761904762,1,1,1,1,0.9782608696,1,1,1,1,0.9642857143,1,0.9736842105,0.9736842105,0.9186046512,0.9146341463,0.987804878,1,0.9880952381,1,0.975,1,1,1,1,0.8947368421,0.9814814815,0.9444444444,0.9107142857,0.9568965517,0.9272727273,0.9649122807,0.9322033898,0.9621212121,0.9615384615,0.962962963,0.9649122807,0.975,0.9326923077,0.9385964912,0.9716981132,0.9909090909,0.9655172414,0.9907407407,0.9692307692,0.9491525424,0.9578313253,0.9539473684,0.9333333333,0.9615384615,0.9871794872,0.9226190476,0.9423076923,0.9864864865,0.9113924051,0.9246575342,0.9701492537,0.9577464789,0.9791666667,0.9507042254,0.972972973,0.9533333333,0.975,0.9933333333,0.9695121951,0.9255319149,0.9210526316,0.9222222222,0.9784946237,0.9540816327,0.9734042553,0.9247311828,0.9293478261,0.972826087,0.9677419355,0.9569892473,0.9285714286,0.9489795918,0.9545454545,0.9945054945,0.9336734694,0.9777777778,0.9090909091,0.9595959596,0.9368932039,0.9090909091,0.9693877551,0.9587155963,0.9684684685,0.9772727273,0.9537037037,0.9567307692,0.9086538462,0.9385964912,0.9902912621,0.975,0.9027777778,0.9782608696,0.95,0.9464285714,0.9490740741,0.9128440367,0.927184466,0.9227272727,0.9201680672,0.9719626168,0.9349315068,0.9728682171,0.9722222222,0.9268292683,0.91796875,0.9666666667,0.9601769912,0.9653846154,0.9028776978,0.9745762712,0.8851851852,0.9338235294,0.9411764706,0.9346153846,0.9666666667,0.9837398374,0.89453125,0.9452054795,0.9078014184,0.9647887324,0.9205298013,0.9612403101,0.921875,0.9468085106,0.9734848485,0.9357142857,0.9125874126,0.9652777778,0.9523809524,0.9383561644,0.9448275862,0.9676258993,0.9362416107,1,1,1,0.9761904762,1,1,0.9736842105,1,1,0.9545454545,1,1,0.9555555556,1,0.9468085106,0.9324324324,1,0.95,0.9857142857,0.9342105263,0.8879310345,1,0.96875,0.8968253968,0.8828125,0.9561403509,0.9375,0.97,0.9561403509,1,0.89375,0.9625,0.9868421053,0.9066666667,0.9802631579,0.9657534247,0.9802631579,0.95,0.9677419355,0.9393939394,0.9431818182,0.9722222222,0.9427083333,0.935483871,0.985,0.925,0.9784946237,0.9388888889,0.9579439252,0.9655172414,0.9587628866,0.9541284404,0.9260869565,0.98,0.9369747899,0.9583333333,0.9692982456,0.963963964,0.9160583942,0.9659090909,0.9671532847,0.9423076923,0.9796747967,0.9365079365,0.937037037,0.9796747967,0.9090909091,0.9566929134,0.988372093,0.9485294118,0.8986928105,0.9161073826,0.9067164179,0.948630137]
# zepBaseline=[0.7857142857,0.8421052632,0.8611111111,0.8235294118,0.8947368421,0.9047619048,0.975,0.9,0.7608695652,0.8684210526,0.8888888889,0.825,0.925,0.8541666667,0.75,0.825,0.8611111111,0.6578947368,0.8913043478,0.85,0.7352941176,0.8375,0.8970588235,0.7142857143,0.9189189189,0.9473684211,0.8684210526,0.8139534884,0.7926829268,0.8536585366,0.9024390244,0.8452380952,0.8529411765,0.8125,0.8472222222,0.8125,0.8461538462,0.8375,0.8947368421,0.9107142857,0.8968253968,0.8125,0.8534482759,0.8706896552,0.8333333333,0.8474576271,0.7651515152,0.8653846154,0.787037037,0.8596491228,0.8333333333,0.875,0.8157894737,0.8773584906,0.8545454545,0.8620689655,0.9259259259,0.8550724638,0.8770491803,0.8253012048,0.7697368421,0.9066666667,0.8205128205,0.83125,0.8546511628,0.8395061728,0.8581081081,0.8333333333,0.7602739726,0.8805970149,0.8661971831,0.8472222222,0.8591549296,0.8513513514,0.8533333333,0.85,0.8666666667,0.8475609756,0.828125,0.8659793814,0.8555555556,0.8421052632,0.87,0.829787234,0.8684210526,0.862244898,0.8532608696,0.8978494624,0.8172043011,0.7871287129,0.8571428571,0.8484848485,0.9037433155,0.806122449,0.8444444444,0.8333333333,0.8737373737,0.8714285714,0.8454545455,0.84,0.8119266055,0.9144144144,0.8318181818,0.875,0.875,0.8644859813,0.7850877193,0.8203883495,0.895,0.8636363636,0.8608695652,0.9,0.90625,0.8703703704,0.8119266055,0.8904761905,0.8090909091,0.8319327731,0.8616071429,0.8529411765,0.8560606061,0.8611111111,0.864,0.90234375,0.8125,0.8672566372,0.8692307692,0.8165467626,0.8347457627,0.7919708029,0.8051470588,0.8388429752,0.8923076923,0.8791666667,0.8333333333,0.83203125,0.8698630137,0.8391608392,0.8482758621,0.8344370861,0.8449612403,0.7578125,0.8125,0.8295454545,0.8601398601,0.8216783217,0.8576388889,0.8707482993,0.8412162162,0.843537415,0.9064748201,0.8355704698,0.8571428571,0.880952381,1,0.7380952381,0.975,0.8157894737,0.7368421053,0.8863636364,0.94,0.7727272727,0.8658536585,0.8705882353,0.829787234,0.8552631579,0.8085106383,0.875,0.75,0.8928571429,0.7428571429,0.7763157895,0.8448275862,0.850877193,0.8671875,0.873015873,0.875,0.8305084746,0.8571428571,0.8,0.8333333333,0.8965517241,0.8353658537,0.8614457831,0.8552631579,0.8181818182,0.9078947368,0.8698630137,0.8289473684,0.85,0.8924731183,0.8415841584,0.8666666667,0.8833333333,0.8697916667,0.8333333333,0.905,0.785,0.90625,0.8722222222,0.8457943925,0.8146551724,0.8505154639,0.8783783784,0.8565217391,0.8785046729,0.8925619835,0.9259259259,0.8464912281,0.8648648649,0.8642857143,0.8795620438,0.8795620438,0.8484848485,0.8821138211,0.8531746032,0.8407407407,0.8821138211,0.847107438,0.8464566929,0.8798449612,0.8368794326,0.8692810458,0.9194630872,0.8492647059,0.8489932886]
# zepConRes=zepConRes[:100]
# zepBaseline=zepBaseline[:100]

# zepConF=[0.9,1,1,1,1,0.9,1,1,0.7,1,1,1,1,0.9,1,1,0.9,1,0.9,0.95,0.95,0.95,1,0.9,0.95,0.85,0.9,0.75,0.8,0.95,1,0.95,1,0.95,0.95,0.9,1,1,0.65,0.8666666667,0.8666666667,0.7333333333,0.8333333333,0.7,0.8333333333,0.8,0.9,0.8,0.9,0.8,0.8666666667,0.7,0.8333333333,0.8333333333,0.9333333333,0.8666666667,0.9333333333,0.8333333333,0.9,0.85,0.8,0.775,0.9,0.95,0.775,0.75,0.875,0.75,0.775,0.85,0.775,0.825,0.85,0.825,0.85,0.95,0.9,0.875,0.78,0.68,0.72,0.9,0.84,0.88,0.72,0.7,0.88,0.82,0.8,0.78,0.78,0.84,0.92,0.78,0.86,0.68,0.84,0.84,0.6166666667,0.8166666667]
# zepBaselineF=[0.4,0.7,0.5,0.5,0.6,0.6,0.9,0.7,0.3,0.6,0.6,0.7,0.7,0.6,0.2,0.5,0.6,0.2,0.7,0.5,0.3,0.45,0.65,0.35,0.65,0.75,0.45,0.4,0.5,0.45,0.6,0.45,0.55,0.35,0.5,0.45,0.5,0.55,0.65,0.6666666667,0.6,0.3,0.4666666667,0.4666666667,0.3666666667,0.5333333333,0.2666666667,0.6666666667,0.3333333333,0.4333333333,0.4,0.4666666667,0.4,0.5333333333,0.5,0.4666666667,0.7333333333,0.4333333333,0.5333333333,0.525,0.25,0.6,0.55,0.5,0.575,0.425,0.525,0.475,0.325,0.575,0.5,0.45,0.525,0.5,0.5,0.575,0.475,0.475,0.38,0.54,0.44,0.5,0.56,0.4,0.52,0.52,0.54,0.6,0.42,0.4,0.5,0.54,0.6,0.38,0.54,0.4,0.54,0.64,0.4,0.4666666667]
# zepConF=zepConF[:100]
# zepBaselineF=zepBaselineF[:100]

zepConRes = []
zepBaseline = []
pc_baseline = open("reach-pc-baseline.csv")
for line in pc_baseline.readlines() :
    fields = line.split(",")
    zepConRes.append(float(fields[0]))
    zepBaseline.append(float(fields[1]))

ax1.set_xlim([0, 1])
ax1.set_ylim([0, 1])

ax1.scatter(zepBaseline, zepConRes, marker="x", s=16, color='#377eb8', label='Score')
#ax1.scatter(zepBaselineF, zepConF, marker="x", s=16, color='#ff7f00', label='Fraction')
ax1.plot([0.0, 1.0], linestyle='--', color="black") 
ax1.set_xlabel('Baseline Score', fontsize=12)
ax1.set_ylabel('PC Score', fontsize=12)
ax1.grid()

#plt.legend(loc='lower right', ncol=1, frameon=False, fontsize=8)

plt.savefig('ospfbaselineresilience.eps', format='eps', dpi=1000, bbox_inches='tight')

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


