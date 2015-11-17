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
        'PLUS','MINUS','EXP', 'TIMES','DIVIDE','EQUALS',
        'LPAREN','RPAREN', 'SEMICOLON', 'COMMA', 'LBRACKET', 'RBRACKET',
        'ISOLATE'     
        )

    # Tokens

    t_PLUS    = r'\+'
    t_MINUS   = r'-'
    t_EXP     = r'\*\*'
    t_TIMES   = r'\*'
    t_DIVIDE  = r'/'
    t_EQUALS  = r'='
    t_LPAREN  = r'\('
    t_RPAREN  = r'\)'
    t_SEMICOLON = r';'
    t_COMMA = r','
    t_LBRACKET = r'\['
    t_RBRACKET = r'\]'
   
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

    # def p_statement_declaration(self, p):
    #     'statement : declaration_statement'
    #     pass

    def p_statement_isolate_varlist(self, p):
        'statement : ISOLATE LPAREN variable RPAREN SEMICOLON'
        pass

    def p_statement_isolate_bivar(self, p):
        'statement : ISOLATE LPAREN variable COMMA variable RPAREN SEMICOLON'
        print "Parsed."
    
    def p_variable_name(self, p):
        'variable : NAME'
        pass
    

    def p_error(self, p):
        print "Syntax error at '%s'" % p.value

if __name__ == '__main__':
    pc = PolicyCompiler()
    pc.run()