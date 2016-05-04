import sys
sys.path.insert(0,"../..")

import readline
import ply.lex as lex
import ply.yacc as yacc
import os
from GenesisAst import *
from NetworkPredicate import *
	
class GPLInterpreter(object):
	def __init__(self, gplfile, topofile, genesisSynthesiser, topology):
		#Parser.__init__(self, name)
		self.gplfile =  open(gplfile)
		self.topofile = open(topofile)
		self.policyTable = dict()
		self.genesisSynthesiser = genesisSynthesiser
		self.topology = topology
		self.tabmodule = "GPLInterpreter" + "_" + "parsetab"
		self.inForLoopFlag = False

		# Build the lexer and parser
		lex.lex(module=self)
		self.gplyacc = yacc.yacc(module=self, tabmodule=self.tabmodule)
		self.topoyacc = yacc.yacc(module=self, tabmodule=self.tabmodule, start = 'topology')

	tokens = (
		'NAME','NUMBER',
		'EQUALS', 'SEP', 'DOT', 'SLASH', 'DOUBLEQUOTE', 'COLON', 'ASSIGN', 'ARROW', 
		'COMMA', 'LBRACKET', 'RBRACKET', 'SEMICOLON',
		'ISOLATE', 'REACH', 'IN',
		'COMMENT', 
		'AND', 'OR', 'NOT', 'TRUE', 'FALSE',
		'MINAVGTE', 'MINMAXTE'
		)

	# Tokens

	t_EQUALS  = r'='
	t_ASSIGN = r'\:='
	t_ARROW = r'\-\>'
	t_SEP = r'=='
	t_DOT = r'\.'
	t_DOUBLEQUOTE = r'\"'
	t_SLASH = r'\/'
	t_COLON = r'\:'
	t_COMMA = r','
	t_SEMICOLON = r';'
	t_LBRACKET = r'\['
	t_RBRACKET = r'\]'
   
	def t_ISOLATE(self, t): r'\|\|'; return t

	def t_REACH(self, t): r'\>\>'; return t

	def t_IN(self, t): r'in'; return t 

	def t_AND(self, t): r'and'; return t 

	def t_OR(self, t): r'or'; return t   

	def t_NOT(self, t): r'not'; return t 

	def t_TRUE(self, t): r'true'; return t 

	def t_FALSE(self, t): r'false'; return t 

	def t_MINAVGTE(self, t): r'minimize-avg-te'; return t

	def t_MINMAXTE(self, t): r'minimize-max-te'; return t

	def t_NAME(self, t):
		r'[a-zA-Z_][a-zA-Z0-9_]*'
		return t

	def t_COMMENT(self, t):
		r'\#.*'
		pass
		# No return value. Token discarded

	def t_NUMBER(self, t):
		r'\d+'
		try:
			t.value = int(t.value)
		except ValueError:
			print "Integer value too large", t.value
			t.value = 0
		#print "parsed number %s" % repr(t.value)
		return t

	t_ignore = " \t"

	def t_newline(self, t):
		r'\n+'
		t.lexer.lineno += t.value.count("\n")
	
	def t_error(self, t):
		print "Illegal character '%s'" % t.value[0]
		t.lexer.skip(1)

	# Parsing rules

	precedence = (
		('left', 'OR'),
		('left', 'AND'),
		('right', 'NOT'),
	)

	def p_program_gpl(self, p):
		'program : gplreach'

	def p_program_gplreach_gplisolate(self, p):
		'program : gplreach SEP gplisolate'
		# for constraint in p[5]:
		#     print constraint.getSw()
		#     self.genesisSynthesiser.addSwitchTablePolicy(constraint.getSw(), constraint.getMaxSize())

	def p_program_gplreach_cons(self, p):
		'program : gplreach SEP constraints'

	def p_program_gplreach_isolate_cons(self, p):
		'program : gplreach SEP gplisolate SEP constraints'
		# for constraint in p[5]:
		#     print constraint.getSw()
		#     self.genesisSynthesiser.addSwitchTablePolicy(constraint.getSw(), constraint.getMaxSize())

	def p_gplreach_stmts(self, p):
		'gplreach : gplreach statement'

	def p_gplreach_stmt(self, p):
		'gplreach : statement'

	def p_statement_reach(self, p):
		'statement : reach_statement'

	# def p_statement_mcast(self, p):
	#     'statement : mcast_statement'

	def p_reach(self, p):
		'reach_statement : NAME ASSIGN predicate COLON NAME REACH NAME'
		# Add Reachability Policy.
		reachPolicy = ReachAst(p[3], p[5], p[7])
		pc = self.genesisSynthesiser.addReachabilityPolicy(predicate=p[3], src=p[5], dst=p[7])
		reachPolicy.setPacketClass(pc)
		self.policyTable[p[1]] = reachPolicy
		p[0] = reachPolicy  

	def p_reach_len(self, p):
		'reach_statement : NAME ASSIGN predicate COLON NAME REACH NAME IN NUMBER'
		# Add Reachability Policy.
		reachPolicy = ReachAst(p[3], p[5], p[7])
		pc = self.genesisSynthesiser.addReachabilityPolicy(predicate=p[3], src=p[5], dst=p[7], pathlen=p[9])
		reachPolicy.setPacketClass(pc)
		self.policyTable[p[1]] = reachPolicy
		p[0] = reachPolicy  

	def p_reach_waypoint(self, p):
		'reach_statement : NAME ASSIGN predicate COLON NAME REACH LBRACKET waypointlist RBRACKET REACH NAME'
		# Add Reachability Policy
		reachPolicy = ReachAst(p[3], p[5], p[11], p[8])
		pc = self.genesisSynthesiser.addReachabilityPolicy(predicate=p[3], src=p[5], dst=p[11], waypoints=p[8])
		reachPolicy.setPacketClass(pc)
		self.policyTable[p[1]] = reachPolicy
		p[0] = reachPolicy  

	def p_reach_waypoint_len(self, p):
		'reach_statement : NAME ASSIGN predicate COLON NAME REACH LBRACKET waypointlist RBRACKET REACH NAME IN NUMBER'
		# Add Reachability Policy.
		reachPolicy = ReachAst(p[3], p[5], p[11], p[8])
		pc = self.genesisSynthesiser.addReachabilityPolicy(predicate=p[3], src=p[5], dst=p[11], waypoints=p[8], pathlen=p[13])
		reachPolicy.setPacketClass(pc)
		self.policyTable[p[1]] = reachPolicy
		p[0] = reachPolicy  

	def p_predicate_and(self, p):
		'predicate : predicate AND predicate'
		p[0] = AndNP(p[1], p[3])

	def p_predicate_or(self, p):
		'predicate : predicate OR predicate'
		p[0] = OrNP(p[1], p[3])

	def p_predicate_not(self, p):
		'predicate : NOT predicate'
		p[0] = NotNP(p[1])

	def p_predicate_true(self, p):
		'predicate : TRUE'
		p[0] = TrueNP()

	def p_predicate_false(self, p):
		'predicate : FALSE'
		p[0] = FalseNP()

	def p_predicate_header(self, p):
		'predicate : NAME DOT NAME EQUALS headervalue'
		header = p[1] + "." + p[3]
		p[0] = EqualNP(header, p[5])

	def p_headervalue_num(self, p):
		'headervalue : NUMBER'
		p[0] = p[1]

	def p_headervalue_ip(self, p):
		'headervalue : ip'
		p[0] = p[1].getIp()

	def p_gplisolate(self, p):
		'gplisolate : gplisolate isolate_statement'

	def p_gplisolate_isolate(self, p):
		'gplisolate : isolate_statement'

	def p_isolate(self, p):
		'isolate_statement : NAME ISOLATE NAME'
		if p[1] in self.policyTable : 
			p1 = self.policyTable[p[1]]
		else :
			print "Policy " + p[1] + " is not defined."
			exit(0)

		if p[3] in self.policyTable : 
			p2 = self.policyTable[p[3]]
		else :
			print "Policy " + p[3] + " is not defined."
			exit(0)

		# Add isolation policy.
		self.genesisSynthesiser.addTrafficIsolationPolicy(p1.getPacketClass(), p2.getPacketClass())

	def p_isolate_allisolated(self, p):
		'isolate_statement : ISOLATE LBRACKET namelist RBRACKET'
		# Check for policies
		for policy in p[3] :
			if not policy in self.policyTable :
				print "Policy " + policy + " is not defined."
				exit(0)

		# Add Policies.
		for i in range(len(p[3])) :
			for j in range(i + 1,len(p[3])) :
				p1 = self.policyTable[ p[3][i] ]
				p2 = self.policyTable[ p[3][j] ]

				# Add isolation policy. 
				self.genesisSynthesiser.addTrafficIsolationPolicy(p1.getPacketClass(), p2.getPacketClass())

	def p_isolate_crossprod(self, p):
		'isolate_statement : LBRACKET namelist RBRACKET ISOLATE LBRACKET namelist RBRACKET'
		# Check for policies
		for policy in p[2] :
			if not policy in self.policyTable :
				print "Policy " + policy + " is not defined."
				exit(0)

		for policy in p[6] :
			if not policy in self.policyTable :
				print "Policy " + policy + " is not defined."
				exit(0)

		# Add Policies.
		for i in range(len(p[2])) :
			for j in range(len(p[6])) :
				p1 = self.policyTable[ p[2][i] ]
				p2 = self.policyTable[ p[6][j] ]

				# Add isolation policy. 
				self.genesisSynthesiser.addTrafficIsolationPolicy(p1.getPacketClass(), p2.getPacketClass())

	# def p_mcast(self, p) :
	#     'mcast_statement : endpoint REACH REACH LBRACKET endpoints RBRACKET' 

	# def p_mcast_equal(self, p):
	#     'mcast_statement : endpoint REACH REACH LBRACKET endpoints RBRACKET IN NUMBER '     

	def p_waypointlist_waypoints(self, p) :
		'waypointlist : waypointlist SEMICOLON waypoints'
		# p[1][len(p[1]) - 1].extend(p[3][0])
		# for i in range(1, len(p[3])) :
		#     p[1].append(p[3][i])
		# p[0] = p[1]
		p[1].append(p[3])
		p[0] = p[1]

	def p_waypointlist(self, p) :
		'waypointlist : waypoints'
		p[0] = [p[1]]

	def p_waypoints(self, p) :
		'waypoints : waypoints COMMA NAME'
		p[1].append(p[3])
		p[0] = p[1]

	def p_waypoints_name(self, p):
		'waypoints : NAME'
		p[0] = [p[1]]

	def p_namelist(self, p) :
		'namelist : namelist COMMA NAME'
		p[1].append(p[3])
		p[0] = p[1]

	def p_namelist_name(self, p):
		'namelist : NAME'
		p[0] = [p[1]]

	def  p_ip_subnet(self, p):
		'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER SLASH NUMBER'
		prefix = str(p[1]) + "." + str(p[3]) + "." + str(p[5]) + "." + str(p[7])
		p[0] = IpAst(prefix, p[9])

	def p_ip_address(self, p):
		'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER'
		address = str(p[1]) + "." + str(p[3]) + "." + str(p[5]) + "." + str(p[7])
		p[0] = IpAst(address)

	def p_constraints(self, p):
		'constraints : constraints constraint'

	def p_constraints_constraint(self, p):
		'constraints : constraint'

	def p_constraint_switch(self, p):
		'constraint : NAME COLON NUMBER'
		# Switch Table Constraint.
		self.genesisSynthesiser.addSwitchTablePolicy(p[1], p[3])

	def p_constraint_link(self, p):
		'constraint : NAME ARROW NAME COLON NUMBER'
		# Switch Table Constraint.
		self.genesisSynthesiser.addLinkCapacityPolicy(p[1], p[3], p[5])

	def p_constraint_te(self, p):
		'constraint : MINAVGTE'
		# Traffic engineering objective: Minimize average utilisation of links
		self.genesisSynthesiser.addTrafficEngineeringObjective(minavg=True)

	def p_constraint_te(self, p):
		'constraint : MINMAXTE'
		# Traffic engineering objective: Minimize the max link utilisation
		self.genesisSynthesiser.addTrafficEngineeringObjective(minmax=True)

	def p_error(self, p):
		print "Syntax error at '%s'" % p.value

	# Topology Parsing rules
	def p_topology_switches(self, p):
		'topology : topology swdesc'

	def p_topology_switch(self, p):
		'topology : swdesc'

	def p_swdesc(self, p):
		'swdesc : NAME COLON LBRACKET swnames RBRACKET'
		neighbours = []
		for sw in p[4]:
			neighbours.append(sw)
		self.topology.addSwitch(p[1], neighbours)

	def p_swdesc_empty(self, p):
		'swdesc : NAME COLON LBRACKET RBRACKET'
		self.topology.addSwitch(p[1], [])

	def p_swnames(self, p):
		'swnames : swnames COMMA NAME'
		p[1].append(p[3])
		p[0] = p[1]

	def p_swnames_name(self, p):
		'swnames : NAME'
		p[0] = [p[1]]

	def getVal(self, name) :
		try :
			""" Deferences a variable to find object"""
			val = self.policyTable[name]
			if not val.getType() == Type.VAR :
				return val
			else :
				return getVal(val.getName())
		except KeyError:
			print name + " is not defined."
			exit(0)
		
	def parseGPL(self) :
		config = self.gplfile.read()
		self.gplyacc.parse(config)

	def parseTopo(self) :
		topo = self.topofile.read()
		self.topoyacc.parse(topo)
	

