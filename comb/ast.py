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

@dataclass
class Sym:
    name: str

    def __str__(self):
        return self.name

    def __hash__(self):
        return hash(self.name)

class ParamTerm:
    def __init__(self, val):
        assert isinstance(val, (Sym, IntValue))
        self.value = val

    def __str__(self):
        return str(self.value)

class Expr:
    def __init__(self, val):
        assert isinstance(val, (Sym, IntValue, ASTCallExpr))
        self.value = val

    def __str__(self):
        return str(self.value)


class Type:
    param_types = []

class IntType(Type):
    def __str__(self):
        return "Int"

class BoolType(Type):
    def __str__(self):
        return "Bool"

class BVType(Type):
    param_types = [IntType]

    def __str__(self):
        return "BV"

@dataclass
class TypeCall:
    type: Type
    pargs : tp.Tuple[ParamTerm]

    def __post_init__(self):
        assert isinstance(self.type, Type)
        assert all(isinstance(parg, ParamTerm) for parg in self.pargs)

    def __str__(self):
        parg_str = ",".join(str(parg) for parg in self.pargs)
        return f"{self.type}[{parg_str}]"


class IntValue:
    type = IntType
    def __init__(self, val):
        assert isinstance(val, int)
        self.value = val

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        return self.value == other.value

@dataclass
class BVValue:
    width: int
    val: int

    def __post_init__(self):
        assert isinstance(self.width, int)
        assert isinstance(self.val, int)

    def __str__(self):
        return f"[{self.width}]\'h{hex(self.val)[2:]}"

    @property
    def type(self):
        raise NotImplementedError()
        return TypeCall[self.width]


#@dataclass
#class ASTType:
#    name : QSym
#    params : tp.Tuple[ParamTerm]
#
#    def __post_init__(self):
#        assert isinstance(self.name, QSym)
#        assert all(isinstance(p, ParamTerm) for p in self.params)
#
#    def __str__(self):
#        if len(self.params)==0:
#            return str(self.name)
#        return f"{self.name}[{_list_to_str(self.params)}]"


@dataclass
class Decl:
    sym: Sym
    type: Type

@dataclass
class ParamDecl(Decl):
    def __post_init__(self):
        assert isinstance(self.sym, Sym)
        if not isinstance(self.type, IntType):
            raise NotImplementedError("Params must be Ints")

    def __str__(self):
        return f"Param {self.sym} : {self.type}"

@dataclass
class InDecl(Decl):
    def __str__(self):
        return f"In {self.sym} : {self.type}"

@dataclass
class OutDecl(Decl):
    def __str__(self):
        return f"Out {self.sym} : {self.type}"


@dataclass
class ASTCallExpr:
    qsym : QSym
    pargs : tp.Tuple[ParamTerm]
    args : tp.Tuple[Expr]

    def __post_init__(self):
        assert isinstance(self.qsym, QSym)
        assert all(isinstance(p, ParamTerm) for p in self.pargs)
        assert all(isinstance(a, Expr) for a in self.args), str(self.args)

class Stmt: pass

@dataclass
class ASTAssignStmt(Stmt):
    lhss: tp.Tuple[Sym]
    rhss: tp.Tuple[Expr]

    def __post_init__(self):
        assert all(isinstance(lhs, Sym) for lhs in self.lhss)
        assert all(isinstance(rhs, Expr) for rhs in self.rhss)



@dataclass
class DeclStmt(Stmt):
    decl: Decl

    def __post_init__(self):
        assert isinstance(self.decl, Decl)

    def __str__(self):
        return str(self.decl)

class Comb:


    def get_type(self, *pvals):
        pass

    def partial_eval(self, *params) -> 'Comb':
        pass

    def io(self, *params):
        pass

    def eval(self, *args):
        pass

    def input_free_vars(self, *params, prefix=""):
        return [self.sym_table[ivar.qsym].free_var(f"{prefix}__{ivar.qsym}") for ivar in self.inputs]

    def output_free_vars(self, prefix=""):
        return [self.sym_table[ivar.qsym].free_var(f"{prefix}__{ivar.qsym}") for ivar in self.outputs]


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

