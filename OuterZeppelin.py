from z3 import *
from Topology import Topology
from PolicyDatabase import PolicyDatabase
from NetworkPredicate import *
import time
import random
import metis
import networkx as nx
from subprocess import *
from collections import deque
import math
import gurobipy as gb
import copy
from collections import defaultdict



class OuterZeppelin(object) :
	def __init__(self, topology, pdb) :
		self.topology = topology
		self.pdb = pdb
 	
 		# Store switch domains for each switch
		self.switchDomains = dict()


	def enforceDAGs(self, dags, endpoints):
		""" Enforce the input destination dags """
		self.destinationDAGs = copy.deepcopy(dags)
		self.endpoints = copy.deepcopy(endpoints)

		start_t = time.time() 


	def calculateLocalPreferences(self) : 
		dsts = self.pdb.getDestinations() 
		





