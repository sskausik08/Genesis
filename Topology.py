class NetworkDatabase(object) :
	""" Database to store the switch mappings to integers """

	def __init__(self) :
		self.switchMap = ["dropSwitch"]
		self.swID = 1
		self.hostMap = dict()

	def insertSwitch(self, swName) :
		self.switchMap.append(swName)
		self.swID += 1
		return self.swID - 1

	def insertHost(self, hostName, swName) :
		sw = self.getSwID(swName)
		hostMap[hostName] = sw

	def getSwID(self, swName) :
		for i in range(len(self.switchMap)) :
			if swName == self.switchMap[i] :
				return i

		raise LookupError(swName + " not in the network database")


	def getSwitchName(self, swID) :
		if swID > len(self.switchMap) - 1 :
			raise LookupError(str(swID) + " is not a valid switch ID")
		else :
			return self.switchMap[swID]

	def getSwitchCount(self) :
		return len(self.switchMap)
	

class Topology(object):
	"Class for a Topology"
	def __init__(self, name="topo-0"):
		self.name = name
		self.networkDatabase = NetworkDatabase()
		self.neighbours = []

		# Add the drop node (node 0) neighbours.
		self.neighbours.append([0])

		# read the topology configuration files
		self.read()


	def getName(self) :
		return self.name

	def read(self) :
		f1 = open("./topoConf/switches")
		lines = f1.readlines()

		# Read the switches file and initialise the network database
		for line in lines : 
			fields = line.split()
			# Inserting switch in the network database
			self.networkDatabase.insertSwitch(fields[0])

			# Initialising the neighbours list for the switch. 
			# Every switch is connected to the "drop switch". 
			self.neighbours.append([0])


		# Read the links of the topology and update the neighbours of each switch
		f2 = open("./topoConf/links") 
		lines = f2.readlines()

		for line in lines : 
			fields = line.split()

			sw1 = self.networkDatabase.getSwID(fields[0])
			sw2 = self.networkDatabase.getSwID(fields[1])

			# Update the neighbour set of both the switches 
			self.neighbours[sw1].append(sw2)
			self.neighbours[sw2].append(sw1)

	def getMaxPathLength(self) :
		return self.getSwitchCount() - 1
		
	def getSwitchCount(self) :
		return self.networkDatabase.getSwitchCount()

	def getSwitchNeighbours(self, swID) :
		return self.neighbours[swID]


t = Topology("a")


