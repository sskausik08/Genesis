from enum import Enum
class Type(Enum):
	VAR = 0
	IP = 1
	SW = 2
	ENDPT = 3
	REACH = 4
	SWLIST = 5
	NUM = 6

class GPLAst(object):
	def __init__(self, type) :
		self.type = type
		self.context = dict()

	def getType(self) :
		return self.type

	def setType(self, type) :
		self.type = type

	def addVariable(self, var) :
		self.context[var] = None

	def inContext(self, var) :
		return var in self.context.keys()

	def addValue(self, var, val) :
		self.context[var] = val

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

class NumberAst(GPLAst):
	def __init__(self, num):
		GPLAst.__init__(self, type=Type.NUM)
		self.num = num

	def getNum(self) :
		return self.num
		
class VariableAst(GPLAst) :
	def __init__(self, name):
		GPLAst.__init__(self, type=Type.VAR)
		self.name = name

	def getName(self) :
		return self.name

class ArrayAst(GPLAst) :
	def __init__(self, name, index):
		GPLAst.__init__(self, type=Type.VAR)
		self.name = name
		self.index = index

	def getName(self) :
		return self.name + "#" + str(self.index)
		
class ReachAst(GPLAst):
	def __init__(self, endpoint1, endpoint2, waypoints=None) :
		GPLAst.__init__(self, type=Type.REACH)
		self.src = endpoint1
		self.dst = endpoint2
		self.waypoints = waypoints

	def getIpEndpoints(self) :
		""" Returns [src.ip, dst.ip] """
		return [self.src.getIp(), self.dst.getIp()]		



