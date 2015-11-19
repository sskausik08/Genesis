import sys
sys.path.insert(0,"../..")

import readline
import ply.lex as lex
import ply.yacc as yacc
import os
from GenesisAst import *
    
class GPLInterpreter(object):
    def __init__(self, name, genesisSynthesiser):
        #Parser.__init__(self, name)
        self.policyFile =  open(name)
        self.variableTable = dict()
        self.genesisSynthesiser = genesisSynthesiser

        # Build the lexer and parser
        lex.lex(module=self)
        yacc.yacc(module=self)

    tokens = (
        'NAME','NUMBER',
        'EQUALS', 'DOT', 'SLASH', 'DOUBLEQUOTE', 'COLON', 
        'LPAREN','RPAREN', 'SEMICOLON', 'COMMA', 'LBRACKET', 'RBRACKET', 'LBRACE', 'RBRACE',
        'ISOLATE', 'REACH'
        )

    # Tokens

    t_EQUALS  = r'='
    t_DOT = r'\.'
    t_DOUBLEQUOTE = r'\"'
    t_SLASH = r'\/'
    t_LPAREN  = r'\('
    t_RPAREN  = r'\)'
    t_SEMICOLON = r';'
    t_COLON = r'\:'
    t_COMMA = r','
    t_LBRACKET = r'\['
    t_RBRACKET = r'\]'
    t_LBRACE = r'\{'
    t_RBRACE = r'\{'
   
    def t_ISOLATE(self, t): r'\|\|'; return t

    def t_REACH(self, t): r'\>\>'; return t

    def t_NAME(self, t):
        r'[a-zA-Z_][a-zA-Z0-9_]*'
        return t

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

    precedence = ()

    def p_program_stmts(self, p):
        'program : program statement'

    def p_program_stmt(self, p):
        'program : statement'

    def p_statement_declaration(self, p):
        'statement : declaration_statement SEMICOLON'

    def p_statement_isolate(self, p):
        'statement : isolate_statement SEMICOLON'

    def p_statement_reach(self, p):
        'statement : reach_statement SEMICOLON'

    def p_declaration_reach(self, p):
        'declaration_statement : variable EQUALS reach_statement'
        var = p[1]
        self.variableTable[var.getName()] = p[3]

    def p_declaration_var(self, p):
        'declaration_statement : variable EQUALS variable'
        lvar = p[1]
        rvar = p[3]
        if rvar.getType == type.VAR :
            print rvar.getName() + " is undeclared."
            exit(0)

        self.variableTable[lvar.getName()] = p[3]

    def p_declaration_endpoint(self, p):
        'declaration_statement : variable EQUALS ipvar COLON swvar'
        var = p[1]
        ip = p[3]
        if not ip.getType == Type.IP : 
            print "Invalid IP variable."
            exit(0)
        sw = p[5] 
        if not sw.getType == Type.SW : 
            print "Invalid SW variable."
            exit(0)
        
        self.variableTable[var.getName()] = EndpointAst(ip, sw)

    def p_declaration_ip(self, p):
        'declaration_statement : variable EQUALS ip'
        var = p[1]
        self.variableTable[var.getName()] = p[3]

    def p_declaration_sw(self, p):
        'declaration_statement : variable EQUALS DOUBLEQUOTE NAME DOUBLEQUOTE'
        var = p[1]
        self.variableTable[var.getName()] = SwAst(p[4])

    def p_isolate_bivar(self, p):
        'isolate_statement :  reachvar ISOLATE reachvar'
        if not p[1].type == Type.REACH or not p[3].type == Type.REACH :
            print "Isolation Policy has incorrect arguments"
            exit(0)

        self.genesisSynthesiser.addTrafficIsolationPolicy(p[1].getIpEndpoints(), p[3].getIpEndpoints())

    def p_reachvar_var(self, p):
        'reachvar : variable'
        p[0] = self.getVal(p[1].getName())

    def p_reachvar_reach(self, p):
        'reachvar : reach_statement'
        p[0] = p[1]

    def p_reach(self, p):
        'reach_statement : endpoint REACH endpoint'
        # Add Reachability Policy.
        if not p[1].type == Type.ENDPT or not p[3].type == Type.ENDPT :
            print "Reach Policy has incorrect arguments"
            exit(0)
        reachPolicy = ReachAst(p[1], p[3])
        self.genesisSynthesiser.addReachabilityPolicy(p[1].getIp(), p[1].getSw(), p[3].getIp(), p[3].getSw())
        p[0] = reachPolicy  

    def p_reach_waypoint(self, p):
        'reach_statement : endpoint REACH LBRACKET swvars RBRACKET REACH endpoint'
        if not p[1].type == Type.ENDPT or not p[7].type == Type.ENDPT :
            print "Reach Policy has incorrect arguments"
            exit(0)
        reachPolicy = ReachAst(p[1], p[7], p[4])
        
        waypoints = []
        for sw in p[4] :
            waypoints.append(sw.getSw())

        self.genesisSynthesiser.addReachabilityPolicy(p[1].getIp(), p[1].getSw(), p[7].getIp(), p[7].getSw(), waypoints) 
        p[0] = reachPolicy 

    def p_endpoint_var(self, p):
        'endpoint : variable'
        p[0] = self.getVal(p[1].getName())

    def p_endpoint_ip_switch(self, p):
        'endpoint : ipvar COLON swvar '
        if not p[1].type == Type.IP :
            print "Endpoint object has incorrect arguments"
            exit(0)
        if not p[3].type == Type.SW : 
            print "Endpoint object has incorrect arguments"
            exit(0)
        p[0] = EndpointAst(p[1], p[3])

    def p_ipvar_ip(self, p):
        'ipvar : ip '
        p[0] = p[1]

    def p_ipvar_var(self, p):
        'ipvar : variable'
        p[0] = self.getVal(p[1].getName())

    def p_swvars(self, p) :
        'swvars : swvars COMMA swvar'
        p[1].append(p[3])
        p[0] = p[1]

    def p_swvars_var(self, p):
        'swvars : swvar'
        p[0] = [p[1]]
    
    def p_swvar_sw(self, p):
        'swvar : DOUBLEQUOTE NAME DOUBLEQUOTE'
        p[0] = SwAst(p[2])
    
    def p_swvar_var(self, p):
        'swvar : variable'
        p[0] = self.getVal(p[1].getName())

    def p_variable_name(self, p):
        'variable : NAME'
        p[0] = VariableAst(p[1])
    
    def  p_ip_subnet(self, p):
        'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER SLASH NUMBER'
        prefix = str(p[1]) + "." + str(p[3]) + "." + str(p[5]) + "." + str(p[7])
        p[0] = IpAst(prefix, p[9])

    def p_ip_address(self, p):
        'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER'
        address = str(p[1]) + "." + str(p[3]) + "." + str(p[5]) + "." + str(p[7])
        p[0] = IpAst(address)

    def p_error(self, p):
        print "Syntax error at '%s'" % p.value

    def getVal(self, name) :
        try :
            """ Deferences a variable to find object"""
            val = self.variableTable[name]
            if not val.getType() == Type.VAR :
                return val
            else :
                return getVal(val.getName())
        except KeyError:
            print name + " is not defined."
            exit(0)
        
    def run(self) :
        config = self.policyFile.read()
        yacc.parse(config)

