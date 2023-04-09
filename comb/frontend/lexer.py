import ply.lex as lex
import ply.yacc as yacc
from .ast import *

#TODO THIS IS ALL WRONG
'''
sym    : VARID
param  : NUMBER | sym
params : param'
        | params COMMA param'
qsym    : NSID'
        | NSID LSQB params RSQB'
type   : 
input   : INPUT sym COLON type'
paramdecl   : PARAM sym COLON type'
paramdecls   : paramdecls paramdecl
inputs  : input'
        | inputs input'
output  : OUTPUT sym COLON type'
outputs : output'
        | outputs output'
bvconst : pterm'd pterm
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
    'BV',
    'CBV',
    'INT',
    'BOOL',
    'COLON',
    'COMMA',
    'NUMBER',
    'LPAREN',
    'RPAREN',
    'ASSIGN',
    'LSQB',
    'RSQB',
    'QHDB',
    'QHVAL',
    'QDVAL',
    'QBVAL',
    'PLUS',
    'MUL',
)

# Regular termession rules for simple tokens
t_COLON   = r':'
t_COMMA   = r','
t_ASSIGN  = r'='
t_LSQB  = r'\['
t_RSQB  = r'\]'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_QHDB = '\'h|\'d|\'b'
t_QHVAL = '\'h[a-f0-9]+'
t_QDVAL = '\'d[0-9]+'
t_QBVAL = '\'b[01]+'
t_PLUS = '\+'
t_MUL = '\*'

_reserved = dict(
    Comb="COMB",
    In="INPUT",
    Out="OUTPUT",
    Param="PARAM",
    BV="BV",
    CBV="CBV",
    Int="INT",
    Bool="BOOL",
)


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
precedence = (
    ('left', 'PLUS'),
    ('left', 'MUL'),
)

def p_sym_0(p):
    'sym : VARID'
    p[0] = Sym(p[1])

def p_syms_0(p):
    'syms : sym'
    p[0] = [p[1]]

def p_syms_1(p):
    'syms : syms COMMA sym'
    p[0] = [*p[1], p[3]]

def p_qsym_0(p):
    'qsym : NSID'
    p[0] = QSym(*p[1])

def p_int_0(p):
    'int : NUMBER'
    p[0] = IntValue(p[1])

def p_bvwidth_0(p):
    'bvwidth : int'
    p[0] = p[1]

def p_bvwidth_1(p):
    'bvwidth : LSQB expr RSQB'
    p[0] = p[2]

def p_bvvalue_0(p):
    'bvvalue : bvwidth QHVAL'
    val = IntValue(int(p[2][2:], 16))
    p[0] = ASTCallExpr(QSym("bv", "const"), [p[1], val], [])

def p_bvvalue_1(p):
    'bvvalue : bvwidth QDVAL'
    val = IntValue(int(p[2][2:], 10))
    p[0] = ASTCallExpr(QSym("bv", "const"), [p[1], val], [])

def p_bvvalue_2(p):
    'bvvalue : bvwidth QBVAL'
    val = IntValue(int(p[2][2:], 2))
    p[0] = ASTCallExpr(QSym("bv", "const"), [p[1], val], [])

def p_bvvalue_3(p):
    'bvvalue : bvwidth QHDB LSQB expr RSQB'
    p[0] = ASTCallExpr(QSym("bv", "const"), [p[1], p[4]], [])

def p_expr_0(p):
    'expr : sym'
    p[0] = p[1]

def p_expr_1(p):
    'expr : int'
    p[0] = p[1]

def p_expr_2(p):
    'expr : callexpr'
    p[0] = p[1]

def p_expr_3(p):
    'expr : expr PLUS expr'
    p[0] = ASTCallExpr(QSym("i", "add"), [], [p[1], p[3]])

def p_expr_4(p):
    'expr : expr MUL expr'
    p[0] = ASTCallExpr(QSym("i", "mul"), [], [p[1], p[3]])

def p_expr_5(p):
    'expr : LPAREN expr RPAREN'
    p[0] = p[2]

def p_exprs_0(p):
    'exprs : expr'
    p[0] = [p[1]]

def p_exprs_1(p):
    'exprs : exprs COMMA expr'
    p[0] = [*p[1], p[3]]

def p_type_0(p):
    'type : INT'
    p[0] = IntType()

def p_type_1(p):
    'type : BOOL'
    p[0] = BoolType()

def p_type_2(p):
    'type : BV LSQB exprs RSQB'
    p[0] = TypeCall(BVType(), p[3])

def p_type_3(p):
    'type : CBV LSQB exprs RSQB'
    p[0] = TypeCall(CBVType(), p[3])


def p_decl_r_0(p):
    'decl_r : sym COLON type'
    p[0] = [p[1], p[3]]

def p_qsym_p_0(p):
    'qsym_p : qsym'
    p[0] = [p[1], []]

def p_qsym_p_1(p):
    'qsym_p : qsym LSQB exprs RSQB'
    p[0] = [p[1], p[3]]

def p_callexpr_0(p):
    'callexpr : qsym_p LPAREN exprs RPAREN'
    p[0] = ASTCallExpr(*p[1], p[3])

def p_callexpr_1(p):
    'callexpr : qsym_p LPAREN RPAREN'
    p[0] = ASTCallExpr(*p[1], [])

def p_callexpr_2(p):
    'callexpr : bvvalue'
    p[0] = p[1]

def p_stmt_0(p):
    'stmt : PARAM decl_r'
    p[0] = ParamDecl(*p[2])

def p_stmt_1(p):
    'stmt : INPUT decl_r'
    p[0] = InDecl(*p[2])

def p_stmt_2(p):
    'stmt : OUTPUT decl_r'
    p[0] = OutDecl(*p[2])

def p_stmt_3(p):
    'stmt : syms ASSIGN exprs'
    p[0] = ASTAssignStmt(p[1], p[3])

def p_stmts_0(p):
    'stmts : stmt'
    p[0] = [p[1]]

def p_stmts_1(p):
    'stmts : stmts stmt'
    p[0] = [*p[1], p[2]]

def p_comb_0(p):
    'comb : COMB qsym stmts'
    p[0] = ASTCombProgram(p[2], p[3])

def p_combs_0(p):
    'combs : comb'
    p[0] = [p[1]]

def p_combs_1(p):
    'combs : combs comb'
    p[0] = [*p[1], p[2]]

def p_obj_0(p):
    'obj : combs'
    p[0] = ASTObj(p[1])

# Error rule for syntax errors
def p_error(p):
    print(f"Syntax error in input!: {p}")

# Build the parser

def get_parser(start='comb'):
    return yacc.yacc(start = start)
