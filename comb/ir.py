import typing as tp
from .ast import Comb, Expr, Sym, QSym, Stmt, DeclStmt, ParamDecl, TypeCall, \
    InDecl, Type, OutDecl, IntValue, _CallExpr, Node, IntType, _list_to_str
from .ast import dataclass
from hwtypes import smt_utils as fc
import pysmt.shortcuts as smt
import functools



def _make_list(v):
    if not isinstance(v, (list, tuple)):
        return [v]
    else:
        return list(v)

def _unwrap_list(v):
    if isinstance(v, (list, tuple)) and len(v)==1:
        return v[0]
    else:
        return v


def ret_list(f):
    @functools.wraps(f)
    def dec(*args, **kwargs):
        return _make_list(f(*args, **kwargs))
    return dec


@dataclass
class CallExpr(_CallExpr):
    comb: Comb
    pargs : tp.Tuple[Expr]
    args : tp.Tuple[Expr]

    def __post_init__(self):
        assert isinstance(self.comb, Comb)
        assert all(isinstance(p, Expr) for p in self.pargs)
        assert all(isinstance(a, Expr) for a in self.args)
        super().__init__(*self.pargs, *self.args)

    def __str__(self):
        parg_str = f"[{_list_to_str(self.pargs)}]"
        if len(self.pargs)==0:
            parg_str = f""
        return f"{self.comb.name}{parg_str}({_list_to_str(self.args)})"

@dataclass
class AssignStmt(Node):
    lhss: tp.Tuple[Sym]
    rhss: tp.Tuple[Expr]

    def __post_init__(self):
        super().__init__(*self.rhss)
        assert all(isinstance(lhs, Sym) for lhs in self.lhss)
        assert all(isinstance(rhs, Expr) for rhs in self.rhss)

    def __str__(self):
        return f"{_list_to_str(self.lhss)} = {_list_to_str(self.rhss)}"


class CombPrimitive(Comb):
    param_types = []

    def __str__(self):
        return f"Comb {self.name}"

#Comb class which has concrete values for params
class CombSpecialized(Comb):
    param_types = []
    def __init__(self, comb: Comb, pargs: tp.Tuple[int]):
        assert isinstance(comb, Comb)
        assert len(pargs) == len(comb.param_types)
        assert all(isinstance(pT, IntType) for pT in comb.param_types)
        assert all(isinstance(parg, int) for parg in pargs)
        self.comb = comb
        self.name = QSym("_", str(comb.name) + "["+", ".join(str(p) for p in pargs) + "]")
        self.pargs = [IntValue(parg) for parg in pargs]

    def get_type(self):
        return self.comb.get_type(*self.pargs)

    @property
    def num_inputs(self) -> int:
        return self.comb.num_inputs

    @property
    def num_outputs(self) -> int:
        return self.comb.num_outputs

    def eval(self, *args, pargs=[]):
        return self.comb.eval(*args, pargs=self.pargs)

    def call_expr(self, pargs, args):
        assert len(pargs) == 0
        return CallExpr(self.comb, self.pargs, args)

    def serialize(self):
        raise NotImplementedError()

    def __str__(self):
        return str(self.name)

'''
Symbol resolution goes from ASTCombProgram -> Comb Program
Turns "bv.add" to the object representing that add

In order to resolve the Comb programs I need to perform type inference at least on the parameters

Type Inference creates types for the current Comb (All other ones already have types)
Type Checking invokes SMT solver
'''

def _flat(l):
    return [l__ for l_ in l for l__ in l_]


from DagVisitor import Visitor
import hwtypes as ht


@dataclass
class CombProgram(Comb):
    name: QSym
    stmts: tp.Tuple[Stmt]

    def __post_init__(self):
        assert all(isinstance(stmt, (AssignStmt, DeclStmt)) for stmt in self.stmts)
        super().__init__(*self.stmts)
        self.type_check()

    @property
    def num_inputs(self):
        return len([stmt for stmt in self.stmts if isinstance(stmt, InDecl)])

    @property
    def num_outputs(self):
        return len([stmt for stmt in self.stmts if isinstance(stmt, OutDecl)])

    def eval(self, *args, pargs=[]):
        from .passes import EvalCombProgram
        e = EvalCombProgram()
        e.run(self, pargs, args)
        return e.outputs()

    @property
    def param_types(self):
        return [stmt.type for stmt in self.stmts if isinstance(stmt, ParamDecl)]



    @functools.lru_cache(None)
    def get_type(self, *pargs):
        assert all(isinstance(parg, Expr) for parg in pargs)
        from .passes import EvalCombProgram
        e = EvalCombProgram()
        args = [Sym(f"I{i}") for i in range(self.num_inputs)]
        e.run(self, pargs, args)
        return e.input_types, e.output_types

    def symbolic_params(self):
        return {stmt.sym.name:stmt.type.free_var(stmt.sym.name) for stmt in self.stmts if isinstance(stmt, ParamDecl)}

    def __str__(self):
        lines = []
        lines.append(f"Comb {self.name}")
        lines += [str(stmt) for stmt in self.stmts]
        return "\n".join(lines)

    def serialize(self):
        return str(self)

    def type_check(self):
        from .passes import EvalCombProgram
        e = EvalCombProgram()
        pargs = [p.free_var(f"P{i}", node=True) for i, p in enumerate(self.param_types)]
        args = [Sym(f"I{i}") for i in range(self.num_inputs)]
        e.run(self, pargs, args)

        tc_conds = []
        def check_types(T0: Type, T1: Type):
            if type(T0) is not type(T1):
                raise ValueError(f"TC ERROR: {T0} != {T1}")
            if isinstance(T0, TypeCall) and isinstance(T1, TypeCall):
                if type(T0.type) != type(T1.type):
                    raise ValueError(f"TC ERROR: {T0} != {T1}")
                if len(T0.pargs) != len(T1.pargs):
                    raise ValueError(f"TC ERROR: {T0} != {T1}")
                for p0, p1 in zip(T0.pargs, T1.pargs):
                    if not (isinstance(p0, IntValue) and isinstance(p1, IntValue)):
                        raise ValueError(f"TC ERROR: {T0} != {T1}")
                    tc_conds.append(ht.SMTInt(p0.value)==ht.SMTInt(p1.value))


        class TypeCheck(Visitor):
            def run(self, node):
                self._dag_cache = set()
                self.visit(node)

            def visit_TypeCall(self, node: TypeCall):
                pTs = _flat(e.expr_to_types[parg] for parg in node.pargs)
                [check_types(T0, T1) for T0, T1 in zip(pTs, node.type.param_types)]

            def visit_CallExpr(self, node: CallExpr):
                pTs = _flat(e.expr_to_types[parg] for parg in node.pargs)
                pvals = _flat(e.expr_to_vals[parg] for parg in node.pargs)
                [check_types(T0, T1) for T0, T1 in zip(pTs, node.comb.param_types)]
                aTs = _flat(e.expr_to_types[arg] for arg in node.args)
                iTs, _ = node.comb.get_type(*pvals)
                [check_types(T0, T1) for T0, T1 in zip(aTs, iTs)]

            def visit_OutDecl(self, node: OutDecl):
                check_types(e.output_to_type[node.sym], e.expr_to_types[node.sym][0])

        TypeCheck().run(self)
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


Modules = {}