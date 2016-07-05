import numpy as np
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

# evenly sampled time at 200ms intervals
x = [10,20,30,40,50,60,70,80]

noTactic1 = [0.18,0.8640999794,2.036143065,16.71143389,643,4005.580206,11894.67818,15000]
noTactic2 = [0.17,0.8066310883, 2.146327019, 21.74198389, 58,211.5037289, 7000, 10000]
noTactic5 = [0.14,0.6872601509,1.693818092,2.794470072,43.64237714,190.4395521,2558,5000]
noTactic10 = [0.13,0.4372241497,1.165225983,2.570262909,4.928798914,6.639307022,453,2353.869107]

markersize = 10
# red dashes, blue squares and green triangles
plt.plot(x, noTactic1, 'r', marker="o", markersize=markersize, label="Group Size:1")
plt.plot(x, noTactic2, 'g', marker="^", markersize=markersize, label="Group Size:2")
plt.plot(x, noTactic5, 'b', marker="h", markersize=markersize, label="Group Size:5")
plt.plot(x, noTactic10, 'y', marker="s", markersize=markersize, label="Group Size:10")


plt.yscale('log')
plt.ylim(ymax=5000)

plt.legend(loc='upper left', frameon=False, fontsize=15)

plt.grid()
plt.savefig('noTacticIsolation.eps', format='eps', dpi=1000)
plt.show()