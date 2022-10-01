import abc
import collections
from dataclasses import dataclass
import typing as tp
import hwtypes as ht


@dataclass
class QSym:
    module: str
    name: str

    def __post_init__(self):
        assert isinstance(self.module, str)
        assert isinstance(self.name, str)

    def __str__(self):
        return f"{self.module}.{self.name}"

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return str(self) == str(other)

class Expr: pass

@dataclass
class Sym(Expr):
    name: str

    def __str__(self):
        return self.name

    def __hash__(self):
        return hash(self.name)

class Type:
    param_types = []

class IntType(Type):
    def __str__(self):
        return "Int"

    def __eq__(self, other):
        return IntType is type(other)

    def free_var(self, name: str):
        return ht.SMTInt(prefix=name)

class BoolType(Type):
    def __str__(self):
        return "Bool"

    def __eq__(self, other):
        return BoolType is type(other)


class BVType(Type):
    param_types = [IntType()]

    def __str__(self):
        return "BV"

    def __eq__(self, other):
        return BVType is type(other)



@dataclass
class TypeCall:
    type: Type
    pargs : tp.Tuple[Expr]

    def __post_init__(self):
        assert isinstance(self.type, Type)
        assert all(isinstance(parg, Expr) for parg in self.pargs)

    def __str__(self):
        parg_str = ",".join(str(parg) for parg in self.pargs)
        return f"{self.type}[{parg_str}]"


class IntValue(Expr):
    type = IntType()
    def __init__(self, val):
        assert isinstance(val, int)
        self.value = val

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        return self.value == other.value

    def get_smt(self):
        return ht.SMTInt(self.value)

class Stmt: pass

@dataclass
class DeclStmt(Stmt):
    sym: Sym
    type: Type

@dataclass
class ParamDecl(DeclStmt):
    def __post_init__(self):
        assert isinstance(self.sym, Sym)
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
        assert isinstance(self.qsym, QSym)
        assert all(isinstance(p, Expr) for p in self.pargs)
        assert all(isinstance(a, Expr) for a in self.args), str(self.args)


@dataclass
class ASTAssignStmt(Stmt):
    lhss: tp.Tuple[Sym]
    rhss: tp.Tuple[Expr]

    def __post_init__(self):
        assert all(isinstance(lhs, Sym) for lhs in self.lhss)
        assert all(isinstance(rhs, Expr) for rhs in self.rhss)
        if len(self.lhss) != len(self.rhss):
            raise TypeError("Assigns must have same arity left and right")

class Comb:

    param_types = None

    def get_type(self, *pvals):
        pass

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


@dataclass
class ASTCombProgram(Comb):
    name: QSym
    stmts: tp.Tuple[Stmt]




#Software Module
class Module:
    name: str

    #@abc.abstractmethod
    #def type_from_sym(self, qsym: QSym) -> 'ASTType':
    #    ...

    @abc.abstractmethod
    def comb_from_sym(self, qsym: QSym) -> 'ASTCombProgram':
        ...

