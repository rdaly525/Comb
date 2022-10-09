import abc
from dataclasses import dataclass
import typing as tp
import hwtypes as ht
from DagVisitor import Visited


dataclass = dataclass(eq=False)

def _list_to_str(l):
    return ", ".join(str(l_) for l_ in l)

class Node(Visited):
    def __init__(self,*args):
        for arg in args:
            if not isinstance(arg, Node):
                raise ValueError(f"{type(arg)}: {arg} not Node")
        assert all(isinstance(arg, Node) for arg in args)
        self._children = args

    def children(self):
        return self._children

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return str(self) == str(other)

    def __str__(self):
        raise NotImplementedError(f"{type(self)} needs to impl __str__")


@dataclass
class QSym(Node):
    module: str
    name: str

    def __post_init__(self):
        assert isinstance(self.module, str)
        assert isinstance(self.name, str)

    def __str__(self):
        return f"{self.module}.{self.name}"

class Expr(Node):

    def __post_init__(self):
        super().__init__()

@dataclass
class Sym(Expr):
    name: str

    def __str__(self):
        return self.name

class Type(Node):
    param_types = []

class IntType(Type):

    def __init__(self):
        super().__init__()
        assert hasattr(self, '__hash__')
        self.__hash__()
        hash(self)

    def __str__(self):
        return "Int"

    def free_var(self, name: str):
        return IntValue(ht.SMTInt(prefix=name))


class BoolType(Type):
    def __str__(self):
        return "Bool"


class BVType(Type):
    param_types = [IntType()]

    def __str__(self):
        return "BV"

    def free_var(self, name, pargs):
        if len(pargs) != 1:
            raise ValueError()
        N = pargs[0]
        if not isinstance(N, IntValue):
            return None
        if not isinstance(N.value, int):
            raise NotImplementedError(f"{N}, the param, needs to be a constant")
        N = N.value
        return BVValue(ht.SMTBitVector[N](prefix=name))


@dataclass
class TypeCall(Node):
    type: Type
    pargs : tp.Tuple[Expr]

    def __post_init__(self):
        super().__init__(*self.pargs)
        assert isinstance(self.type, Type)
        assert all(isinstance(parg, Expr) for parg in self.pargs)

    def __str__(self):
        parg_str = ",".join(str(parg) for parg in self.pargs)
        return f"{self.type}[{parg_str}]"

    def free_var(self, name):
        return self.type.free_var(name, self.pargs)

class BVValue(Expr):
    type = BVType()
    def __init__(self, val):
        super().__init__()
        assert isinstance(val, ht.SMTBitVector)
        self.value = val

    def __str__(self):
        return f"BVValue: {self.value}"

class IntValue(Expr):
    type = IntType()
    def __init__(self, val):
        super().__init__()
        assert isinstance(val, (int, ht.SMTInt))
        self.value = val

    def __str__(self):
        return str(self.value)

    #def __eq__(self, other):
    #    return self.value == other.value

    def get_smt(self):
        return ht.SMTInt(self.value)

class Stmt(Node): pass

@dataclass
class DeclStmt(Stmt):
    sym: Sym
    type: Type

    def __post_init__(self):
        assert isinstance(self.sym, Sym)
        super().__init__(self.type)

@dataclass
class ParamDecl(DeclStmt):
    def __post_init__(self):
        super().__post_init__()
        if not isinstance(self.type, IntType):
            raise NotImplementedError("Params currently must be Ints")

    def __str__(self):
        return f"Param {self.sym} : {self.type}"

@dataclass
class InDecl(DeclStmt):

    def __str__(self):
        return f"In {self.sym} : {self.type}"

@dataclass
class OutDecl(DeclStmt):
    def __str__(self):
        return f"Out {self.sym} : {self.type}"

class _CallExpr(Expr): pass

@dataclass
class ASTCallExpr(_CallExpr):
    qsym : QSym
    pargs : tp.Tuple[Expr]
    args : tp.Tuple[Expr]

    def __post_init__(self):
        super().__init__(self.qsym, *self.pargs, *self.args)
        assert isinstance(self.qsym, QSym)
        assert all(isinstance(p, Expr) for p in self.pargs)
        assert all(isinstance(a, Expr) for a in self.args), str(self.args)

    def __str__(self):
        parg_str = f"[{_list_to_str(self.pargs)}]"
        if len(self.pargs)==0:
            parg_str = f""
        return f"{self.qsym}{parg_str}({_list_to_str(self.args)})"



@dataclass
class ASTAssignStmt(Stmt):
    lhss: tp.Tuple[Sym]
    rhss: tp.Tuple[Expr]

    def __post_init__(self):
        super().__init__(*self.lhss, *self.rhss)
        assert all(isinstance(lhs, Sym) for lhs in self.lhss)
        assert all(isinstance(rhs, Expr) for rhs in self.rhss)

    def __str__(self):
        return f"{_list_to_str(self.lhss)} = {_list_to_str(self.rhss)}"

class Obj:
    def __init__(self, combs):
        super().__init__(self, *combs)
        assert all(isinstance(comb, Comb) for comb in combs)
        self.comb_dict = {comb.name:comb for comb in combs}


class Comb(Node):
    param_types = []

    def get_type(self, *pvals):
        raise NotImplementedError()

    @property
    def has_params(self):
        return len(self.param_types) > 0

    def eval(self, *args, pargs=[]):
        raise NotImplementedError()

    def create_symbolic_inputs(self, *pvals):
        iTs, _ = self.get_type(*pvals)
        return [T.free_var(f"I{i}") for i, T in enumerate(iTs)]


    #def partial_eval(self, *params) -> 'Comb':
    #    pass

    #def io(self, *params):
    #    pass

    #def eval(self, *args):
    #    pass

    #def input_free_vars(self, *params, prefix=""):
    #    return [self.sym_table[ivar.qsym].free_var(f"{prefix}__{ivar.qsym}") for ivar in self.inputs]

    #def output_free_vars(self, prefix=""):
    #    return [self.sym_table[ivar.qsym].free_var(f"{prefix}__{ivar.qsym}") for ivar in self.outputs]


#@dataclass(unsafe_hash=True)
@dataclass
class ASTCombProgram(Comb):
    name: QSym
    stmts: tp.Tuple[Stmt]

    def __post_init__(self):
        super().__init__(*self.stmts)

    def __str__(self):
        return f"ASTComb {self.name}: {[str(stmt) for stmt in self.stmts]}"

    #def __hash__(self):
    #    return hash(str(self))

#Software Module
class Module:
    name: str

    #@abc.abstractmethod
    #def type_from_sym(self, qsym: QSym) -> 'ASTType':
    #    ...

    @abc.abstractmethod
    def comb_from_sym(self, qsym: QSym) -> 'ASTCombProgram':
        ...

