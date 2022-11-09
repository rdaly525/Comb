from .lexer import get_parser, lexer
from .passes import SymRes, VerifyNoAST

def compile_program(program: str, debug=False, yacc_start='comb'):
    parser = get_parser(yacc_start)
    acomb = parser.parse(program, lexer=lexer, debug=debug)
    if acomb is None:
        raise ValueError("Syntax Error!!!")
    comb = symbol_resolution(acomb)
    return comb


def symbol_resolution(acomb):
    comb = SymRes().run(acomb)
    VerifyNoAST().run(comb)
    return comb