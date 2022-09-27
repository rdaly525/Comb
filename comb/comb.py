import abc
import collections
import re
from dataclasses import dataclass
import typing as tp
import hwtypes as ht

#class ParamType:
#    pass
#
#class Nat(ParamType): pass


class Param:
    pass

class NatType:
    param_types = ()

class Nat(Param):
    def __init__(self, value):
        if isinstance(value, int) and value > 0:
            pass
        elif isinstance(value, str):
            pass
        else:
            raise ValueError("Bad Value")
        self.value = value

    def __str__(self):
        return str(self.value)

    def __eq__(self, other):
        return self.value == other.value

@dataclass
class BVConst:
    width: Nat
    val: int

    def __str__(self):
        if isinstance(self.width.value, int):
            return f"{self.width}\'h{hex(self.val)[2:]}"
        return f"[{self.width}]\'h{hex(self.val)[2:]}"


@dataclass
class QSym:
    ns: str
    name: str

    def __str__(self):
        return f"{self.ns}.{self.name}"

    def __hash__(self):
        return hash(str(self))

    def __eq__(self, other):
        return str(self) == str(other)


#Software Module
class Module:
    name: str

    @abc.abstractmethod
    def type_from_sym(self, qsym: QSym) -> 'Type':
        ...

    @abc.abstractmethod
    def comb_from_sym(self, qsym: QSym) -> 'CombFun':
        ...

def _list_to_str(l):
    return ", ".join(str(l_) for l_ in l)

@dataclass
class Call:
    name : QSym
    params : tp.Tuple[Param]
    args : tp.Tuple[str]

    def __str__(self):
        return f"{self.name}[{_list_to_str(self.params)}]({_list_to_str(self.args)})"


@dataclass
class Type:
    name : QSym
    params : tp.Tuple[Param]

    def __str__(self):
        if len(self.params)==0:
            return str(self.name)
        return f"{self.name}[{_list_to_str(self.params)}]"


@dataclass
class Var:
    name: str
    type: Type

    def __str__(self):
        return f"{self.name} : {self.type}"

class Stmt: pass

@dataclass
class Assign(Stmt):
    lhss: tp.Tuple[str]
    call: Call

    @property
    def args(self):
        return self.call.args

    def __str__(self):
        return f"{_list_to_str(self.lhss)} = {self.call}"

class ParamAssign(Assign): pass

class Comb:

    def partial_eval(self, *params) -> 'Comb':
        pass

    def io(self, *params):
        pass

    def eval(self, *args):
        pass

    def input_free_vars(self, *params, prefix=""):
        return [self.sym_table[ivar.name].free_var(f"{prefix}__{ivar.name}") for ivar in self.inputs]

    def output_free_vars(self, prefix=""):
        return [self.sym_table[ivar.name].free_var(f"{prefix}__{ivar.name}") for ivar in self.outputs]


class Prim(Comb):
    commutative = False


@dataclass
class Decl(Stmt):
    var: Var

class ParamDecl(Decl):
    def __str__(self):
        return f"Param {self.var}"

class InDecl(Decl):
    def __str__(self):
        return f"In {self.var}"

class OutDecl(Decl):
    def __str__(self):
        return f"Out {self.var}"

@dataclass
class CombFun(Comb):
    name: QSym
    #params: tp.Tuple[Var]
    #inputs: tp.Tuple[Var]
    #outputs: tp.Tuple[Var]
    stmts: tp.Tuple[Stmt]

    @property
    def has_params(self):
        return len(self.params) > 0

    def param_types(self):
        raise NotImplementedError()

    def create_symbolic_inputs(self):
        return (self.sym_table[ivar.name].free_var(ivar.name) for ivar in self.inputs)

    def serialize(self):
        lines = []
        lines.append(f"Comb {self.name}")
        lines += [str(stmt) for stmt in self.stmts]
        return "\n".join(lines)

    #Only evaling for SMT
    def eval(self, *args):
        assert len(args) == len(self.inputs)
        val_table = {var.name:arg for arg, var in zip(args, self.inputs)}
        def get_val(arg):
            if isinstance(arg, BVConst):
                return ht.SMTBitVector[arg.width](arg.val)
            else:
                return val_table[arg]
        for stmt in self.stmts:
            args = [get_val(arg) for arg in stmt.args]
            vals = self.ext_ops[stmt.op].eval(*args)
            assert isinstance(vals, tuple)
            assert len(vals) == len(stmt.lhss)
            for val, sym in zip(vals, stmt.lhss):
                val_table[sym] = val
        return tuple(val_table[var.name] for var in self.outputs)

    def __post_init__(self):
        self.params = [d.var for d in self.stmts if isinstance(d, ParamDecl)]
        self.inputs = [d.var for d in self.stmts if isinstance(d, InDecl)]
        self.outputs = [d.var for d in self.stmts if isinstance(d, OutDecl)]

        #p_valid = all(isinstance(d, ParamDecl) for d in self.decls[:len(self.params)])
        #i_valid = all(isinstance(d, InDecl) for d in self.decls[len(self.params):-len(self.outputs)])
        #o_valid = all(isinstance(d, OutDecl) for d in self.decls[-len(self.outputs):])
        #if not (p_valid and i_valid and o_valid):
        #    raise TypeError("Params, then Ins, then Outs")
        self.resolve_qualified_symbols()
        self.type_inference()
        self.type_check()

    #Makes sure all the QSym symbols exist (ops and types)
    def resolve_qualified_symbols(self):
        #Default Modules
        from .modules import BitVectorModule, ParamModule
        self.modules = {'bv':BitVectorModule(), 'p':ParamModule()}

        def resolve_comb(qsym):
            if qsym.ns not in self.modules:
                raise ValueError("Missing module ", qsym.ns)
            return self.modules[qsym.ns].comb_from_sym(qsym)

        def resolve_type(qsym):
            if qsym.ns not in self.modules:
                raise ValueError("Missing module ", qsym.ns)
            return self.modules[qsym.ns].type_from_sym(qsym)

        #Resolve Ops
        self.qsym_to_comb = {}
        self.qsym_to_type = {}
        for stmt in self.stmts:
            if isinstance(stmt, Decl):
                type_name: QSym = stmt.var.type.name
                self.qsym_to_type[type_name] = resolve_type(type_name)
            else:
                assert isinstance(stmt, Assign)
                comb_name = stmt.call.name
                self.qsym_to_comb[comb_name] = resolve_comb(comb_name)


    #Get the types (possibly parameterized) of all symbols
    # This will:
    #   Do a parameter type check
    #       Both type check param assignments and parameters of value assignments
    #   Checks that all the symbols are defined before used and outputs assigned
    #   Verify param inputs on calls trace from params
    #   Verify that args trace from inputs
    def type_inference(self):
        self.p_sym_table = {} #VARID -> Type
        self.v_sym_table = {} #VARID -> Type

        # Verify that the type params exist as a Constant or in p_sym_table
        #TODO This is assuming that the param is a Nat
        def param_check(param_types, param_values):
            if len(param_types) != len(param_values):
                raise ValueError("Mismatch in params")
            for pt, pv in zip(param_types, param_values):
                if isinstance(pv, Nat) and pt is not NatType:
                    raise TypeError(f"{pv} is not of type {pt}")
                if isinstance(pv.value, str) and pv.value not in self.p_sym_table:
                    raise TypeError(f"{pv} used before defined")

        outputs = {}
        param_decls = {}
        param_assigns = {}
        in_decls = {}
        out_decls = {}
        value_assigns = {}
        for i, stmt in enumerate(self.stmts):
            if isinstance(stmt, ParamDecl):
                param_decls[i] = stmt
                name = stmt.var.name
                t_name = stmt.var.type.name
                t_params = stmt.var.type.params
                if len(t_params) > 0:
                    raise NotImplementedError("Param types cannot be parametrized")
                if name in self.p_sym_table:
                    raise TypeError(f"Redefinition of {name}")
                self.p_sym_table[name] = self.qsym_to_type[t_name]()
            elif isinstance(stmt, (InDecl, OutDecl)):
                name = stmt.var.name
                t_name = stmt.var.type.name
                t_params = stmt.var.type.params
                t_cls = self.qsym_to_type[t_name]
                param_check(t_cls.param_types, t_params)
                if name in self.v_sym_table:
                    raise TypeError(f"Redefinition of {name}")
                if isinstance(stmt, OutDecl):
                    out_decls[i] = stmt
                    outputs[name] = t_cls(*t_params)
                else:
                    in_decls[i] = stmt
                    self.v_sym_table[name] = t_cls(*t_params)
            elif isinstance(stmt, Assign):
                comb = self.qsym_to_comb[stmt.call.name]
                if len(comb.input_types(*stmt.call.params)) != len(stmt.call.args):
                    raise TypeError("Mismatch in number of args")

                #Determine if this is a param_call or an arg call
                p_call = all(isinstance(arg, str) and arg in self.p_sym_table for arg in stmt.args)
                if p_call:
                    param_assigns[i] = stmt
                    #Type check the arguments
                else:
                    if not all(isinstance(arg, str) and arg in self.v_sym_table for arg in stmt.args):
                        raise ValueError(f"{stmt} has arg used before defined")
                param_check(comb.param_types, stmt.call.params)
                output_types = comb.output_types(*stmt.call.params)
                if len(stmt.lhss) != len(output_types):
                    raise TypeError("Mismatch in number of outputs")
                for lhs, output_type in zip(stmt.lhss, output_types):
                    if lhs in self.v_sym_table:
                        raise TypeError(f"Redefinition of {name}")
                    self.v_sym_table[lhs] = output_type
            else:
                assert 0
        for oname in outputs:
            if oname not in self.v_sym_table:
                raise TypeError(f"Output {oname} never assigned")

    #Gather all the args and add to a list of things they need to equal
    def type_check(self):
        from .modules import BVType
        tc = collections.defaultdict(list)
        consts = []
        for sym, t in self.v_sym_table.items():
            tc[sym].append(t)
        for stmt in self.stmts:
            if isinstance(stmt, Assign):
                input_types = self.qsym_to_comb[stmt.call.name].input_types(*stmt.call.params)
                assert len(stmt.call.args) == len(input_types)
                for arg, t in zip(stmt.call.args, input_types):
                    if isinstance(arg, BVConst):
                        consts.append([t,BVType(arg.width)])
                    else:
                        tc[arg].append(t)
        print(tc)
        print(consts)
        assert 0