class NetworkPredicate(object):
	def __init__(self, val=None):
		self.value = None

	def set(self, val):
		self.value = val


class AndNP(NetworkPredicate):
	def __init__(self, op1, op2):
		NetworkPredicate.__init__(self)
		self.op1 = op1
		self.op2 = op2

	def evaluate(self, pktheaders):
		return self.op1.evaluate(pktheaders) and self.op2.evaluate(pktheaders)

	def getStr(self):
		return self.op1.getStr() + " AND " + self.op2.getStr()

class OrNP(NetworkPredicate):
	def __init__(self, op1, op2):
		NetworkPredicate.__init__(self)
		self.op1 = op1
		self.op2 = op2

	def evaluate(self, pktheaders):
		return self.op1.evaluate(pktheaders) or self.op2.evaluate(pktheaders)

	def getStr(self):
		return self.op1.getStr() + " OR " + self.op2.getStr()

class NotNP(NetworkPredicate):
	def __init__(self, op):
		NetworkPredicate.__init__(self)
		self.op = op

	def evaluate(self, pktheaders):
		return not self.op.evaluate(pktheaders)

	def getStr(self):
		return "NOT " + self.op.getStr()

class EqualNP(NetworkPredicate):
	def __init__(self, header, val):
		NetworkPredicate.__init__(self)
		self.header = header
		self.headervalue = val

	def evaluate(self, pktheaders):
		for h in pktheaders :
			# h is a tuple : first field is header name, second field is header value.
			if self.header == h[0] :
				# Header matches. Check if value matches
				if self.headervalue == h[1] :
					return True
		return False

	def getStr(self):
		return self.header + " = " + str(self.headervalue)

class TrueNP(NetworkPredicate):
	def __init__(self):
		NetworkPredicate.__init__(self, True)

	def evaluate(self, pktheaders):
		return True
	
	def getStr(self):
		return "true"


class FalseNP(NetworkPredicate):
	def __init__(self):
		NetworkPredicate.__init__(self, True)

	def evaluate(self, pktheaders):
		return False

	def getStr(self):
		return "false"
		
