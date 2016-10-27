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


x = range(46)

OptFig = plt.figure(1)

config = [0.6526586621, 0.5666364461, 0.3657678781, 0.3825757576, 0.3874396135, 0.3986074848, 0.6278434941, 0.4825367647, 0.302869288, 0.416772554, 0.6258426966, 0.6666666667, 0.4933962264, 0.6379310345, 0.6944954128, 0.5827338129, 0.4718562874, 0.559599636, 0.5859073359, 0.5836466165, 0.4398148148, 0.419525066, 0.5455445545, 0.4319852941, 0.4166666667, 0.3369175627, 0.5387797311, 0.4056872038, 0.4246323529, 0.390569395, 0.4585930543, 0.7800829876, 0.7656903766, 0.6960148285, 0.4299568966, 0.8654037886, 0.6616961789, 0.872311828, 0.9710610932, 0.6511397423, 0.3691099476, 0.603046595, 0.6327967807, 0.430324277, 0.9378084896, 0.675397567]

rf = [0.5222551929, 0.6717791411, 1, 0.75, 0.8891509434, 0.8320158103, 0.598540146, 0.7899543379, 1, 1.024657534, 0.5404699739, 0.5825242718, 0.7888198758, 0.4672897196, 0.6777777778, 0.537084399, 1.008928571, 0.7674418605, 1, 0.6862068966, 0.9732142857, 1.018134715, 0.88, 1.008264463, 0.9105145414, 1.106951872, 0.6333333333, 0.7918552036, 0.9392523364, 0.8298676749, 0.9058171745, 0.5251572327, 0.3987730061, 0.6538461538, 1.007772021, 0.3511904762, 0.5098039216, 0.7585470085, 0.4556213018, 0.5605700713, 0.9959349593, 0.5701357466, 0.6728395062, 0.941025641, 0.3116531165, 0.651741293]


# markersize = 11

plt.plot(x, config, '#ff7f00', label="B/W Configuration Size")
plt.plot(x, rf, '#377eb8', label="B/W Route Filter Count")

plt.legend(loc='upper left', frameon=False, fontsize=18)

plt.xlabel('Reading', fontsize=20)
plt.ylabel('Ratio of Best/Worst Metric', fontsize=20)

plt.grid()
plt.savefig('mcmcOpt.eps', format='eps', dpi=1000, bbox_inches='tight')

