import sys
sys.path.insert(0,"../..")

import readline
import ply.lex as lex
import ply.yacc as yacc
import os

class Parser:
    """
    Base class for a lexer/parser that has the rules defined as methods
    """
    tokens = ()
    precedence = ()

    def __init__(self, **kw):
        if not len(sys.argv) == 2 :
            print "Usage : python PolicyCompiler.py <name--of-configuration-file>"
            exit(0)
        self.configFile = open(sys.argv[1])
        self.debug = kw.get('debug', 0)
        self.names = { }
        try:
            modname = os.path.split(os.path.splitext(__file__)[0])[1] + "_" + self.__class__.__name__
        except:
            modname = "parser"+"_"+self.__class__.__name__
        self.debugfile = modname + ".dbg"
        self.tabmodule = modname + "_" + "parsetab"
        print self.debugfile, self.tabmodule

        # Build the lexer and parser
        lex.lex(module=self, debug=self.debug)
        yacc.yacc(module=self,
                  debug=self.debug,
                  debugfile=self.debugfile,
                  tabmodule=self.tabmodule)

    def run(self):
        config = self.configFile.read()
        yacc.parse(config)

    
class PolicyCompiler(Parser):

    tokens = (
        'NAME','NUMBER',
        'EQUALS', 'DOT', 'SLASH', 'DOUBLEQUOTE',
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
    t_COMMA = r','
    t_LBRACKET = r'\['
    t_RBRACKET = r'\]'
    t_LBRACE = r'\{'
    t_RBRACE = r'\{'
   
    def t_ISOLATE(self, t): r'isolate'; return t

    def t_REACH(self, t): r'reach'; return t

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
        #self.names[p[1]] = p[3]
        pass

    def p_program_stmt(self, p):
        'program : statement'
        pass

    def p_statement_declaration(self, p):
        'statement : declaration_statement'
        pass

    def p_statement_isolate(self, p):
        'statement : isolate_statement'
        pass

    def p_statement_reach(self, p):
        'statement : reach_statement'
        pass

    def p_declaration_reach(self, p):
        'declaration_statement : variable EQUALS reach_statement'
        pass

    def p_declaration_ip(self, p):
        'declaration_statement : variable EQUALS ip SEMICOLON'
        pass

    def p_declaration_sw(self, p):
        'declaration_statement : variable EQUALS DOUBLEQUOTE NAME DOUBLEQUOTE SEMICOLON'
        pass

    def p_isolate_varlist(self, p):
        'isolate_statement : ISOLATE LPAREN variable RPAREN SEMICOLON'
        pass

    def p_isolate_bivar(self, p):
        'isolate_statement : ISOLATE LPAREN variable COMMA variable RPAREN SEMICOLON'
        print "Parsed."

    def p_reach(self, p):
        'reach_statement : REACH LPAREN ipvar COMMA ipvar COMMA swvar COMMA swvar COMMA swvarlist RPAREN SEMICOLON'
        pass  

    def p_ipvar_ip(self, p):
        'ipvar : ip'
        pass
    
    def p_ipvar_var(self, p):
        'ipvar : variable'
        pass

    def p_swarlist(self, p):
        'swvarlist : LBRACKET swvar RBRACKET'
        pass
    
    def p_swvar_sw(self, p):
        'swvar : DOUBLEQUOTE NAME DOUBLEQUOTE'
        pass
    
    def p_swvar_var(self, p):
        'swvar : variable'
        pass

    def p_variable_name(self, p):
        'variable : NAME'
        pass
    
    def  p_ip_subnet(self, p):
        'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER SLASH NUMBER'
        print "Subnet"
        pass

    def p_ip_address(self, p):
        'ip : NUMBER DOT NUMBER DOT NUMBER DOT NUMBER'
        print "address"
        pass

    def p_error(self, p):
        print "Syntax error at '%s'" % p.value

if __name__ == '__main__':
    pc = PolicyCompiler()
    pc.run()