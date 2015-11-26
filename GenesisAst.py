from enum import Enum
class Type(Enum):
	VAR = 0
	IP = 1
	SW = 2
	ENDPT = 3
	REACH = 4
	CSRT = 5

class GPLAst(object):
	def __init__(self, type) :
		self.type = type
		self.context = dict()

	def getType(self) :
		return self.type

	def setType(self, type) :
		self.type = type

class IpAst(GPLAst) :
	def __init__(self, prefix, plen=32) :
		GPLAst.__init__(self, type=Type.IP)
		self.prefix = prefix
		self.plen = plen 

	def printAst(self) :
		print self.prefix + "/" + str(self.plen)

	def getIp(self) :
		return self.prefix + "/" + str(self.plen)

class SwAst(GPLAst) :
	def __init__(self, name) :
		GPLAst.__init__(self, type=Type.SW)
		self.sw = name

	def getSw(self) :
		return self.sw

class EndpointAst(GPLAst):
	def __init__(self, ip, sw):
		GPLAst.__init__(self, type=Type.ENDPT)
		self.ip = ip
		self.sw = sw

	def getIp(self) :
		return self.ip.getIp()

	def getSw(self) :
		return self.sw.getSw()
		
class VariableAst(GPLAst) :
	def __init__(self, name):
		GPLAst.__init__(self, type=Type.VAR)
		self.name = name

	def getName(self) :
		return self.name
		
class ReachAst(GPLAst):
	def __init__(self, predicate, src, dst, waypoints=None) :
		GPLAst.__init__(self, type=Type.REACH)
		self.src = src
		self.dst = dst
		self.match = predicate
		self.waypoints = waypoints
		self.pc = -1

	def setPacketClass(self, pc):
		self.pc = pc

	def getPacketClass(self):
		return self.pc

class ConstraintAst(GPLAst):
	def __init__(self, name, size):
		GPLAst.__init__(self, type=Type.CSRT)
		self.sw = name
		self.maxSize = size

	def getSw(self) :
		return self.sw

	def getMaxSize(self):
		return self.maxSize

