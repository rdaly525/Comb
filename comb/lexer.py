import ply.lex as lex
import ply.yacc as yacc
import typing as tp
from .comb import *

'''
sym    : VARID
param  : NUMBER | sym
params : param'
        | params COMMA param'
qsym    : NSID'
        | NSID LSQB params RSQB'
type   : qsym
input   : INPUT sym COLON type'
paramdecl   : PARAM sym COLON type'
paramdecls   : paramdecls paramdecl
inputs  : input'
        | inputs input'
output  : OUTPUT sym COLON type'
outputs : output'
        | outputs output'
bvconst : pexpr'd pexpr
arg : sym | BVCONST
args : arg
     | args COMMA arg'
stmt : args ASSIGN op LPAREN args RPAREN'
stmts : stmt'
      | stmts stmt'
'''


# List of token names.   This is always required
tokens = (
    'NSID',
    'VARID',
    'COMB',
    'INPUT',
    'OUTPUT',
    'PARAM',
    'COLON',
    'COMMA',
    'NUMBER',
    'BVCONST',
    'LPAREN',
    'RPAREN',
    'ASSIGN',
    'LSQB',
    'RSQB',
)

# Regular expression rules for simple tokens
t_COLON   = r':'
t_COMMA   = r','
t_ASSIGN  = r'='
t_LSQB  = r'\['
t_RSQB  = r'\]'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'

_reserved = dict(
    Comb="COMB",
    In="INPUT",
    Out="OUTPUT",
    Param="PARAM",
)

def t_BVCONST(t):
    r'\'h[0-9a-f]+'
    t.value = int(t.value[2:],16)
    return t

def t_VARID(t):
    r'[a-zA-Z_][a-zA-Z0-9_\.]*'
    kind = _reserved.get(t.value)
    if kind is not None:
        t.type = kind
    else:
        vals = t.value.split(".")
        if len(vals) > 1:
            t.type = "NSID"
            t.value = vals
        else:
            assert len(vals) == 1
            t.type = "VARID"
    return t

#import re
##like 13'h23
#def parse_bv(s):
#    m = re.search(r'([1-9]\d+)\'h([0-9a-f]*)',s)
#    assert m is not None
#    width = int(m.group(1))
#    val = int(m.group(2))
#    assert 0 <= val < 2**width
#    return BVConst(width, val)

def t_NUMBER(t):
    r'\d+'
    t.value = int(t.value)
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()

#YACC
start = 'comb'


def p_sym_0(p):
    'sym : VARID'
    p[0] = p[1]

def p_param_0(p):
    'param : NUMBER'
    p[0] = Nat(p[1])

def p_param_1(p):
    'param : sym'
    p[0] = Nat(p[1])

def p_params_0(p):
    'params : param'
    p[0] = [p[1]]

def p_params_1(p):
    'params : params COMMA param'
    p[0] = p[1] + [p[3]]

def p_qsym_0(p):
    'qsym : NSID'
    p[0] = QSym(*p[1])


def p_qsym_p_0(p):
    'qsym_p : qsym'
    p[0] = [p[1], []]

def p_qsym_p_1(p):
    'qsym_p : qsym LSQB params RSQB'
    p[0] = [p[1], p[3]]

def p_type_0(p):
    'type : qsym_p'
    p[0] = Type(*p[1])

def p_decl_r_0(p):
    'decl_r : sym COLON type'
    p[0] = Var(p[1], p[3])

def p_param_d_0(p):
    'param_d : PARAM decl_r'
    p[0] = p[2]

# input ::= input <varid> : <type>
def p_input_d_0(p):
    'input_d : INPUT decl_r'
    p[0] = p[2]

# output ::= output <varid> : <type>
def p_output_d_0(p):
    'output_d : OUTPUT decl_r'
    p[0] = p[2]

def p_decl_0(p):
    'decl : param_d'
    p[0] = ParamDecl(p[1])

def p_decl_1(p):
    'decl : input_d'
    p[0] = InDecl(p[1])

def p_decl_2(p):
    'decl : output_d'
    p[0] = OutDecl(p[1])

def p_decls_0(p):
    'decls : decl'
    p[0] = [p[1]]

def p_decls_1(p):
    'decls : decls decl'
    p[0] = p[1] + [p[2]]

def p_bvwidth_0(p):
    'bvwidth : NUMBER'
    p[0] = Nat(p[1])

def p_bvwidth_1(p):
    'bvwidth : LSQB param RSQB'
    p[0] = p[2]

def p_bvconst_0(p):
    'bvconst : bvwidth BVCONST'
    p[0] = BVConst(p[1], p[2])

def p_const_0(p):
    'const : bvconst'
    p[0] = p[1]

def p_const_1(p):
    'const : NUMBER'
    p[0] = int(p[1])

def p_arg_0(p):
    'arg : sym'
    p[0] = p[1]

def p_arg_1(p):
    'arg : const'
    p[0] = p[1]

def p_args_0(p):
    'args : arg'
    p[0] = [p[1]]

def p_args_1(p):
    'args : args COMMA arg'
    p[0] = p[1] + [p[3]]

def p_call_0(p):
    'call : qsym_p LPAREN args RPAREN'
    p[0] = Call(*p[1], p[3])

def p_stmt_0(p):
    'stmt : decl'
    p[0] = p[1]

def p_stmt_1(p):
    'stmt : args ASSIGN call'
    p[0] = Assign(p[1], p[3])

def p_stmts_0(p):
    'stmts : stmt'
    p[0] = [p[1]]

def p_stmts_1(p):
    'stmts : stmts stmt'
    p[0] = p[1] + [p[2]]

# comb ::= <comb> <nsid> <stmts>
def p_comb_0(p):
    'comb : COMB qsym stmts'
    p[0] = CombFun(p[2], p[3])

# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

# Build the parser
parser = yacc.yacc()


def program_to_comb(program: str, debug=False, type_check=False) -> CombFun:
    comb = parser.parse(program, lexer=lexer, debug=debug)
    if comb is None:
        raise ValueError("Syntax Error!")
    if type_check:
        comb.type_check()
    return comb

