from comb.frontend.ast import ASTObj, QSym, Module
from comb.frontend.ir import Obj
from comb.frontend.lexer import get_parser, lexer
from comb.frontend.passes import SymRes, VerifyNoAST
from comb.frontend.stdlib import GlobalModules


def compile_program(program: str, debug=False) -> Obj:
    yacc_start = 'obj'
    parser = get_parser(yacc_start)
    aobj = parser.parse(program, lexer=lexer, debug=debug)
    if aobj is None:
        raise ValueError("Syntax Error!!!")
    obj = symbol_resolution(aobj)
    return obj


def symbol_resolution(aobj: ASTObj) -> Obj:
    modules = {}
    for acomb in aobj.combs:
        cname: QSym = acomb.name
        if cname.module in GlobalModules:
            raise NotImplementedError("Cannot redefine pre-existing modules: " + str(cname))
        if cname.module not in modules:
            modules[cname.module] = Module(cname.module)
    obj = SymRes(modules).run(aobj)
    VerifyNoAST().run(obj)
    return obj