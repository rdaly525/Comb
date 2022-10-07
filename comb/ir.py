import typing as tp
from .ast import Comb, Expr, Sym, QSym, Stmt, DeclStmt, ASTCombProgram, ASTAssignStmt, ParamDecl, TypeCall, \
    IntType, InDecl, Type, OutDecl, ASTCallExpr, IntValue, _CallExpr, BoolType, Obj, Node, _list_to_str
from dataclasses import dataclass
from hwtypes import smt_utils as fc
import pysmt.shortcuts as smt
import functools



def ret_list(f):
    @functools.wraps(f)
    def dec(*args, **kwargs):
        ret = f(*args, **kwargs)
        if not isinstance(ret, (list, tuple)):
            return [ret]
        else:
            return list(ret)
    return dec

@dataclass
class CallExpr(_CallExpr):
    comb: Comb
    pargs : tp.Tuple[Expr]
    args : tp.Tuple[Expr]

    def __post_init__(self):
        assert isinstance(self.comb, Comb)
        assert all(isinstance(p, Expr) for p in self.pargs)
        assert all(isinstance(a, Expr) for a in self.args), str(self.args)

    def __str__(self):
        parg_str = f"[{_list_to_str(self.pargs)}]"
        if len(self.pargs)==0:
            parg_str = f""
        return f"{self.comb.name}{parg_str}({_list_to_str(self.args)})"


@dataclass
class AssignStmt:
    lhss: tp.Tuple[Sym]
    rhss: tp.Tuple[Expr]

    @property
    def args(self):
        return self.call.args

    def __str__(self):
        return f"{_list_to_str(self.lhss)} = {_list_to_str(self.rhss)}"



class CombPrimitive(Comb):
    commutative = False
    param_types = []

'''
Symbol resolution goes from ASTCombProgram -> Comb Program
Turns "bv.add" to the object representing that add

In order to resolve the Comb programs I need to perform type inference at least on the parameters

Type Inference creates types for the current Comb (All other ones already have types)
Type Checking invokes SMT solver
'''

def _flat(l):
    return [l__ for l_ in l for l__ in l_]


@dataclass
class CombProgram(Comb):
    name: QSym
    stmts: tp.Tuple[Stmt]

    def __post_init__(self):
        assert all(isinstance(stmt, (AssignStmt, DeclStmt)) for stmt in self.stmts)
        #Generate the type signature
        self.type_inference()

        #invokes solver
        self.type_check()

    @property
    def param_types(self):
        return [stmt.type for stmt in self.stmts if isinstance(stmt, ParamDecl)]

    def get_type(self, *pvals):
        #I need to account for parameters that are not thje same
        raise NotImplementedError("THIS IS HARD")

    def symbolic_params(self):
        return {stmt.sym.name:stmt.type.free_var(stmt.sym.name) for stmt in self.stmts if isinstance(stmt, ParamDecl)}

    def sym_eval(self, **vals):
        vals = {**vals}
        def do_sym(sym: Sym):
            return [vals.get(sym.name, None)]
        def do_expr(expr: Expr):
            if isinstance(expr, Sym):
                return do_sym(expr)
            elif isinstance(expr, IntValue):
                return [expr.get_smt()]
            else:
                assert isinstance(expr, CallExpr)
                if len(expr.pargs) > 0:
                    return None
                arg_vals = _flat([do_expr(arg) for arg in expr.args])
                if None in arg_vals:
                    return None
                return expr.comb.eval(*arg_vals)

        for stmt in self.stmts:
            if isinstance(stmt, AssignStmt):
                rhs_vals = [do_expr(rhs) for rhs in stmt.rhss]
                if None in rhs_vals:
                    continue
                for lhs, rhs_val in zip(stmt.lhss, rhs_vals):
                    vals[lhs.name] = rhs_val
        return vals

    def serialize(self):
        lines = []
        lines.append(f"Comb {self.name}")
        lines += [str(stmt) for stmt in self.stmts]
        return "\n".join(lines)


    def type_inference(self):
        #str -> type
        self.sym_table = {}
        def check_sym(sym: Sym):
            if sym not in self.sym_table:
                raise ValueError(f"{sym} used before declared")
            return self.sym_table[sym]

        def check_type(T: Type):
            if isinstance(T, TypeCall):
                if len(T.pargs) != len(T.type.param_types):
                    raise ValueError(f"{T}: wrong param arity")
                Ts = _flat(check_expr(parg) for parg in T.pargs)
                for argT, pT in zip(Ts, T.type.param_types):
                    if isinstance(pT, TypeCall):
                        raise NotImplementedError()
                    if argT != pT:
                        raise ValueError(f"TC ERROR: {T} param types")


        def check_expr(expr: Expr):
            if isinstance(expr, IntValue):
                return [expr.type]
            elif isinstance(expr, Sym):
                T = check_sym(expr)
                return [T]
            elif isinstance(expr, CallExpr):
                if len(expr.pargs) != len(expr.comb.param_types):
                    raise ValueError(f"{expr}: wrong param arity")
                Ts = _flat(check_expr(parg) for parg in expr.pargs)
                for argT, pT in zip(Ts, expr.comb.param_types):
                    if isinstance(pT, TypeCall):
                        raise NotImplementedError()
                    if argT != pT:
                        raise ValueError(f"TC ERROR: {expr} param types")

                itypes, otypes = expr.comb.get_type(*expr.pargs)
                arity = sum(len(check_expr(arg)) for arg in expr.args)
                if len(itypes) != arity:
                    raise ValueError(f"{expr}: wrong input arity")
                return otypes
            else:
                raise NotImplementedError(f"{expr} {type(expr)}")


        outputs = {}
        for stmt in self.stmts:
            if isinstance(stmt, DeclStmt):
                decl = stmt
                T = decl.type
                check_type(T)
                if isinstance(decl, OutDecl):
                    if decl.sym in outputs:
                        raise ValueError(f"{decl.sym}: Redefined")
                    outputs[decl.sym] = T
                else:
                    if decl.sym in self.sym_table:
                        raise ValueError(f"{decl.sym}: Redefined")
                    self.sym_table[decl.sym] = T
            elif isinstance(stmt, AssignStmt):
                Ts = _flat(check_expr(rhs) for rhs in stmt.rhss)
                if len(Ts) != len(stmt.lhss):
                    raise ValueError(f"{stmt}: Wrong assignment arity")
                for lhs, T in zip(stmt.lhss, Ts):
                    if lhs in self.sym_table:
                        raise ValueError(f"{decl.sym}: Redefined")
                    self.sym_table[lhs] = T
            else:
                raise NotImplementedError(stmt)

        for sym in outputs:
            if sym not in self.sym_table:
                raise TypeError(f"Out {sym}: never assigned!")

    def type_check(self):
        vals = self.symbolic_params()
        vals = self.sym_eval(**vals)


        @ret_list
        def eval_sym(sym: Sym):
            assert sym.name in vals
            return vals[sym.name]

        @ret_list
        def eval_expr(expr: Expr):
            if isinstance(expr, Sym):
                return eval_sym(expr)
            elif isinstance(expr, IntValue):
                return expr.get_smt()
            else:
                assert isinstance(expr, CallExpr)
                assert len(expr.pargs) == 0
                arg_vals = _flat([eval_expr(arg) for arg in expr.args])
                ret = expr.comb.eval(*arg_vals)
                return ret

        tc_conds = []
        # I need to type check statment inputs
        def check_types(T0: Type, T1: Type):
            if type(T0) is not type(T1):
                return False
            if isinstance(T0, IntType) and isinstance(T1, IntType):
                return True
            if isinstance(T0, BoolType) and isinstance(T1, BoolType):
                return True
            assert isinstance(T0, TypeCall) and isinstance(T1, TypeCall)
            if type(T0.type) != type(T1.type):
                return False
            if len(T0.pargs) != len(T1.pargs):
                return False
            for p0, p1 in zip(T0.pargs, T1.pargs):
                for e0, e1 in zip(eval_expr(p0), eval_expr(p1)):
                    tc_conds.append(e0==e1)

            return True

        @ret_list
        def get_type(expr: Expr):
            if isinstance(expr, Sym):
                return self.sym_table[expr]
            elif isinstance(expr, IntValue):
                return IntType()
            elif isinstance(expr, CallExpr):
                exp_Ts, out_Ts = expr.comb.get_type(*expr.pargs)
                arg_Ts = _flat(get_type(arg) for arg in expr.args)
                for eT, aT in zip(exp_Ts, arg_Ts):
                    if not check_types(eT, aT):
                        raise TypeError(f"ERROR TC: {eT} != {aT}")
                return out_Ts

        for stmt in self.stmts:
            if isinstance(stmt, AssignStmt):
                [get_type(rhs) for rhs in stmt.rhss]

            if isinstance(stmt, OutDecl):
                check_types(get_type(stmt.sym)[0], stmt.type)

        f_fc = fc.And(tc_conds)
        f = f_fc.to_hwtypes()
        if f.value.is_constant() and f.value.constant_value() is True:
            return
        print(f_fc.serialize())
        with smt.Solver(name='z3') as solver:
            solver.add_assertion((~f).value)
            res = solver.solve()
            if res is False:
                return
            raise TypeError(f"TC: Type check failed: \n{f.serialize()}")

    @property
    def param_syms(self):
        return [stmt.sym for stmt in self.stmts if isinstance(stmt, ParamDecl)]

    @property
    def in_syms(self):
        return [stmt.sym for stmt in self.stmts if isinstance(stmt, InDecl)]

    def partial_eval(self, *pargs):
        vals = {}
        for psym, pval in zip(self.param_syms, pargs):
            vals[psym] = IntValue(pval)
        stmts = []
        def eval_expr(expr: Expr):
            if isinstance(expr, Sym):
                if expr in vals:
                    return [vals[expr]]
                return [expr]
            elif isinstance(expr, IntValue):
                return [expr]
            elif isinstance(expr, CallExpr):
                pvals = _flat(eval_expr(pexpr) for pexpr in expr.pargs)
                call_args = _flat(eval_expr(aexpr) for aexpr in expr.args)
                call_rets = _make_list(expr.comb.eval(*call_args, pargs=pvals))


        def get_type(T: Type):
            if isinstance(T, TypeCall):
                pvals = [eval_expr(parg) for parg in T.pargs]
                return TypeCall(T.type, pvals)
            return T

        for stmt in self.stmts:
            if isinstance(stmt, ParamDecl):
                pass
            elif isinstance(stmt, InDecl):
                InDecl(stmt.sym, get_type(stmt.type))

            if isinstance(astmt, DeclStmt):
                stmt = astmt
                if isinstance(astmt.type, TypeCall):
                    new_pargs = [resolve_expr(parg) for parg in astmt.type.pargs]
                    new_T = TypeCall(astmt.type.type, new_pargs)
                    stmt = type(astmt)(astmt.sym, new_T)
            elif isinstance(astmt, ASTAssignStmt):
                new_exprs = [resolve_expr(rhs) for rhs in astmt.rhss]
                stmt = AssignStmt(astmt.lhss, new_exprs)
            else:
                raise ValueError(f"{astmt}: {type(astmt)}")
            stmts.append(stmt)
        return CombProgram(acomb.name, stmts)

    def eval(self, *args, pargs=[]):
        vals = {}
        for psym, pval in zip(self.param_syms, pargs):
            vals[psym] = pval
        for sym, val in zip(self.in_syms, args):
            vals[sym] = val

        for stmt in self.stmts:
            pass


Modules = {}
#from .modules import BitVectorModule, ParamModule
#
#self.modules = {'bv': BitVectorModule(), 'p': ParamModule()}
from DagVisitor import Visitor

class SymRes(Visitor):

    def run(self, node: Node):
        assert isinstance(node, Node)
        self._dag_cache = set()
        self.new_node = {}
        self.visit(node)
        return self.new_node[node]

    def generic_visit(self, node):
        Visitor.generic_visit(self, node)
        self.new_node[node] = node

    def visit_QSym(self, qsym: QSym):
        if qsym.module not in Modules:
            raise ValueError("Missing module ", qsym.module)
        self.new_node[qsym] = Modules[qsym.module].comb_from_sym(qsym)

    def visit_ASTCallExpr(self, expr: ASTCallExpr):
        Visitor.generic_visit(self, expr)
        call_comb = self.new_node[expr.qsym]
        new_pargs = [self.new_node[arg] for arg in expr.pargs]
        new_args = [self.new_node[arg] for arg in expr.args]
        new_expr = CallExpr(call_comb, new_pargs, new_args)
        self.new_node[expr] = new_expr

    def visit_TypeCall(self, node: TypeCall):
        Visitor.generic_visit(self, node)
        new_pargs = [self.new_node[parg] for parg in node.pargs]
        new_T = TypeCall(self.new_node[node.type], new_pargs)
        self.new_node[node] = new_T

    def visit_ASTAssignStmt(self, node: ASTAssignStmt):
        Visitor.generic_visit(self, node)
        new_rhss = [self.new_node[rhs] for rhs in node.rhss]
        new_lhss = [self.new_node[lhs] for lhs in node.lhss]
        new_stmt = AssignStmt(new_lhss, new_rhss)
        self.new_node[node] = new_stmt

    def visit_ASTCombProgram(self, acomb: ASTCombProgram):
        from . import stdlib
        stmts = [self.new_node[stmt] for stmt in acomb.stmts]
        return CombProgram(acomb.name, stmts)

    def visit_Obj(self, obj: Obj):
        return Obj([self.new_node[comb] for comb in obj])

def resolve_qsym(qsym):
    if qsym.module not in Modules:
        raise ValueError("Missing module ", qsym.module)
    return Modules[qsym.module].comb_from_sym(qsym)

def resolve_expr(expr: Expr):
    if isinstance(expr, ASTCallExpr):
        acexpr = expr
        call_comb = resolve_qsym(acexpr.qsym)
        new_pargs = [resolve_expr(arg) for arg in acexpr.pargs]
        new_args = [resolve_expr(arg) for arg in acexpr.args]
        return CallExpr(call_comb, new_pargs, new_args)
    return expr

def symbol_resolution(acomb: ASTCombProgram) -> CombProgram:
    print(str(acomb))
    return SymRes().run(acomb)

#def symbol_resolution(acomb: ASTCombProgram) -> CombProgram:
#    from . import stdlib
#    if isinstance(acomb, Obj):
#        combs = [symbol_resolution(comb) for comb in acomb.comb_dict.values()]
#        return Obj(combs)
#    assert isinstance(acomb, ASTCombProgram)
#    stmts = []
#    for astmt in acomb.stmts:
#        if isinstance(astmt, DeclStmt):
#            stmt = astmt
#            if isinstance(astmt.type, TypeCall):
#                new_pargs = [resolve_expr(parg) for parg in astmt.type.pargs]
#                new_T = TypeCall(astmt.type.type, new_pargs)
#                stmt = type(astmt)(astmt.sym, new_T)
#        elif isinstance(astmt, ASTAssignStmt):
#            new_exprs = [resolve_expr(rhs) for rhs in astmt.rhss]
#            stmt = AssignStmt(astmt.lhss, new_exprs)
#        else:
#            raise ValueError(f"{astmt}: {type(astmt)}")
#        stmts.append(stmt)
#    return CombProgram(acomb.name, stmts)
