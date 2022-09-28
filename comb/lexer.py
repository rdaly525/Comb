import ply.lex as lex
import ply.yacc as yacc
import typing as tp
from .ast import *

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
    p[0] = Sym(p[1])

def p_syms_0(p):
    'syms : sym'
    p[0] = [p[1]]

def p_syms_1(p):
    'syms : syms COMMA sym'
    p[0] = [*p[1], p[2]]

def p_qsym_0(p):
    'qsym : NSID'
    p[0] = QSym(*p[1])

def p_nat_0(p):
    'nat : NUMBER'
    p[0] = NatValue(p[1])

def p_pexpr_0(p):
    'pexpr : nat'
    p[0] = ParamExpr(p[1])

def p_pexpr_0(p):
    'pexpr : sym'
    p[0] = ParamExpr(p[1])

def p_pexprs_0(p):
    'pexprs : pexpr'
    p[0] = [p[1]]

def p_pexprs_1(p):
    'pexprs : pexprs COMMA pexpr'
    p[0] = [*p[1], p[3]]

def p_bvwidth_0(p):
    'bvwidth : nat'
    p[0] = ParamExpr(p[1])

def p_bvwidth_1(p):
    'bvwidth : LSQB pexpr RSQB'
    p[0] = p[2]

def p_bvvalue_0(p):
    'bvvalue : bvwidth BVCONST'
    p[0] = BVValue(p[1], p[2])

def p_const_0(p):
    'const : bvvalue'
    p[0] = p[1]

def p_const_1(p):
    'const : nat'
    p[0] = p[1]

def p_expr_0(p):
    'expr : sym'
    p[0] = Expr(p[1])

def p_expr_1(p):
    'expr : const'
    p[0] = Expr(p[1])

def p_exprs_0(p):
    'exprs : expr'
    p[0] = [p[1]]

def p_exprs_1(p):
    'exprs : exprs COMMA expr'
    p[0] = [*p[1], p[3]]

def p_qsym_p_0(p):
    'qsym_p : qsym'
    p[0] = [p[1], []]

def p_qsym_p_1(p):
    'qsym_p : qsym LSQB pexprs RSQB'
    p[0] = [p[1], p[3]]

def p_type_0(p):
    'type : qsym_p'
    p[0] = ASTType(*p[1])

def p_decl_r_0(p):
    'decl_r : sym COLON type'
    p[0] = [p[1], p[3]]

def p_decl_0(p):
    'decl : PARAM decl_r'
    p[0] = ParamDecl(*p[2])

def p_decl_1(p):
    'decl : INPUT decl_r'
    p[0] = InDecl(*p[2])

def p_decl_2(p):
    'decl : OUTPUT decl_r'
    p[0] = OutDecl(*p[2])

def p_callexpr_0(p):
    'callexpr : qsym_p LPAREN exprs RPAREN'
    p[0] = ASTCallExpr(*p[1], p[3])

def p_stmt_0(p):
    'stmt : decl'
    p[0] = ASTDeclStmt(p[1])

def p_stmt_1(p):
    'stmt : syms ASSIGN callexpr'
    p[0] = ASTAssignStmt(p[1], p[3])

def p_stmts_0(p):
    'stmts : stmt'
    p[0] = [p[1]]

def p_stmts_1(p):
    'stmts : stmts stmt'
    p[0] = [*p[1], p[2]]

# comb ::= <comb> <nsid> <stmts>
def p_comb_0(p):
    'comb : COMB qsym stmts'
    p[0] = ASTCombProgram(p[2], p[3])

# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

# Build the parser
parser = yacc.yacc()


def program_to_comb(program: str, debug=False) -> ASTCombProgram:
    comb = parser.parse(program, lexer=lexer, debug=debug)
    if comb is None:
        raise ValueError("Syntax Error!")
    return comb

