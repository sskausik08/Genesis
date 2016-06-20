from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import networkx as nx
import copy
import math


""" Generating random dags for Zeppelin """

class ZeppelinInputGenerator(object) :
	def __init__(self, topo, pdb, pcRange) :
		self.topology = topo
		self.pdb = pdb

		swCount = self.topology.getSwitchCount()
		edgeSwitches = (topology.getSwitchCount() * 2/ 5) - 1  
		self.endpoints = []
		for pc in range(pcRange) :




