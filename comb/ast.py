import abc
from dataclasses import dataclass
import typing as tp
import hwtypes as ht
from DagVisitor import Visited


dataclass = dataclass(eq=False)

def _list_to_str(l):
    return ", ".join(str(l_) for l_ in l)

class Node(Visited):
    def __init__(self, *args):
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

class Type(Node): pass

class IntType(Type):

    def __init__(self):
        super().__init__()
        assert hasattr(self, '__hash__')
        self.__hash__()
        hash(self)

    def __str__(self):
        return "Int"

    def free_var(self, name: str, node: bool=False):
        ret = ht.SMTInt(prefix=name)
        if node:
            ret = IntValue(ret)
        return ret

class BoolType(Type):
    def __str__(self):
        return "Bool"


class ParameterizedType(Node):
    param_types = []

class BVType(ParameterizedType):
    param_types = [IntType()]

    def __str__(self):
        return "BV"

    def free_var(self, name, pargs, node: bool=False):
        if len(pargs) != 1:
            raise ValueError()
        N = pargs[0]
        if not isinstance(N, IntValue):
            return None
        if not isinstance(N.value, int):
            raise NotImplementedError(f"{N}, the param, needs to be a constant")
        N = N.value
        ret = ht.SMTBitVector[N](prefix=name)
        if node:
            ret = BVValue(ret)
        return ret


@dataclass
class TypeCall(Node):
    type: ParameterizedType
    pargs : tp.Iterable[Expr]

    def __post_init__(self):
        super().__init__(*self.pargs)
        assert isinstance(self.type, ParameterizedType)
        assert all(isinstance(parg, Expr) for parg in self.pargs)

    def __str__(self):
        parg_str = ",".join(str(parg) for parg in self.pargs)
        return f"{self.type}[{parg_str}]"

    def free_var(self, name, node: bool=False):
        return self.type.free_var(name, self.pargs, node)

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
    pargs : tp.Iterable[Expr]
    args : tp.Iterable[Expr]

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
    lhss: tp.Iterable[Sym]
    rhss: tp.Iterable[Expr]

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
    commutative = False
    param_types = []
    def __init__(self, *args):
        super().__init__(*args)
        self.partial_cache = {}

    def get_type(self, *pvals):
        raise NotImplementedError()

    @property
    def num_inputs(self) -> int:
        return NotImplementedError()

    @property
    def num_outputs(self) -> int:
        return NotImplementedError()

    @property
    def has_params(self):
        return len(self.param_types) > 0

    #All values must be Node types
    def eval(self, *args, pargs=[]):
        raise NotImplementedError()

    #All values are the underlying type
    #args contains pargs followed by args
    #Params must be python ints
    #args must be either python ints or hwtypes.AbstractBitVector
    def evaluate(self, *args):
        def from_raw(v, T):
            if isinstance(v, (int, ht.SMTInt)):
                if not isinstance(T, IntType):
                    raise ValueError(f"TC: {v} should be of type {T}")
                return IntValue(v)
            elif isinstance(v, ht.SMTBitVector):
                if not isinstance(T, TypeCall) or T.type is not BVType and T.pargs != [IntValue(v.size)]:
                    raise ValueError(f"TC: {v} should be of type {T}")
                return BVValue(v)
            else:
                raise NotImplementedError(f"{v}: {type(v)} not supported")
        def to_raw(v):
            return v.value

        N = len(self.param_types)
        if len(args) != N + self.num_inputs:
            raise ValueError("Wrong Number of inputs")
        pargs = [from_raw(v, self.param_types[i]) for i, v in enumerate(args[:N])]
        iTs, oTs = self.get_type(*pargs)
        args = [from_raw(v, iTs[i]) for i, v in enumerate(args[N:])]
        rets = self.eval(*args, pargs=pargs)
        rets = [to_raw(v) for v in rets]
        if len(rets)==1:
            rets = rets[0]
        return rets

    def create_symbolic_inputs(self, *pvals, node: bool=False, prefix="In"):
        iTs, _ = self.get_type(*pvals)
        return [T.free_var(f"{prefix}_{i}", node) for i, T in enumerate(iTs)]

    def create_symbolic_outputs(self, *pvals, node: bool=False, prefix="Out"):
        _, oTs = self.get_type(*pvals)
        return [T.free_var(f"{prefix}_{i}", node) for i, T in enumerate(oTs)]

    def partial_eval(self, *pargs):
        if not all(isinstance(parg, int) for parg in pargs):
            raise NotImplementedError("partial eval only on ints")
        if len(pargs) != len(self.param_types):
            raise NotImplementedError()
        from .ir import CombSpecialized
        return CombSpecialized(self, pargs)

    def __getitem__(self, item):
        if not isinstance(item, tuple):
            item = (item,)
        return self.partial_eval(*item)

    def call_expr(self, pargs, args):
        from .ir import CallExpr
        return CallExpr(self, pargs, args)



#@dataclass(unsafe_hash=True)
@dataclass
class ASTCombProgram(Comb):
    name: QSym
    stmts: tp.Iterable[Stmt]

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


#Contains a set of module declarations, comb definitions, etc...
class Object:
    modules: tp.List[Module]


