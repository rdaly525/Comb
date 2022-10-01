import typing as tp
from .ast import Comb, ParamTerm, Expr, Sym, QSym, Stmt, DeclStmt, ASTCombProgram, ASTAssignStmt, ParamDecl, TypeCall, \
    IntType, InDecl, Type, OutDecl, BVValue, ASTCallExpr
from dataclasses import dataclass

def _list_to_str(l):
    return ", ".join(str(l_) for l_ in l)


def type_check_params(call, pargs, sym_table):
    ptypes = call.param_types
    if len(pargs) != len(ptypes):
        raise ValueError(f"{call.name} bad param values")
    for parg, ptype in zip(pargs, ptypes):
        if isinstance(parg, Sym):
            if parg not in sym_table:
                raise ValueError(f"{parg} used before declared")
            T = sym_table[parg]
        else:
            T = parg.type
        if ptype != T:
            raise ValueError(f"Parameter {parg} does not typecheck")


@dataclass
class CallExpr:
    comb: Comb
    pargs : tp.Tuple[ParamTerm]
    args : tp.Tuple[Expr]
    def __str__(self):
        return f"{self.comb.name}[{_list_to_str(self.pargs)}]({_list_to_str(self.args)})"


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
In order to resolve the Comb programs I need to perform type inference at least on the parameters


Type Inference creates types for the current Comb (All other ones already have types)
Type Checking invokes SMT solver

Problem: I cannot define functions that *return* parameters. 
Sol 1:
    Relax typing rules for parameter inputs
    #More complex eval (almost surely turns into a dependently typed langauge) Maybe not...
    #Simple looking language
    #Distinction between a parameter and a normal arg is now sketch
'''


@dataclass
class CombProgram(Comb):
    name: QSym
    stmts: tp.Tuple[Stmt]

    def __post_init__(self):
        assert all(isinstance(stmt, (AssignStmt, DeclStmt)) for stmt in self.stmts)
        #Generate the type signature
        #self.type_inference()

        #Envokes solver
        self.type_check()

    @property
    def param_types(self):
        raise NotImplementedError()

    def serialize(self):
        lines = []
        lines.append(f"Comb {self.name}")
        lines += [str(stmt) for stmt in self.stmts]
        return "\n".join(lines)


    def type_inference(self):
        #str -> type
        self.sym_table = {}
        def check_type(T: Type):
            if isinstance(T, TypeCall):
                pval = T.N.value
                if isinstance(pval, Sym):
                    if pval not in self.sym_table:
                        raise ValueError(f"{pval} used before declared")
                    if not isinstance(self.sym_table[pval], IntType):
                        raise NotImplementedError(f"All Params ({pval}) must be type Int")
        outputs = {}
        for stmt in self.stmts:
            #if isinstance(stmt, (ParamDecl, InDecl, OutDecl)):
            if isinstance(stmt, DeclStmt):
                decl = stmt.decl
                T = decl.type
                if isinstance(T, TypeCall):
                    type_check_params(T.type, T.pargs, self.sym_table)
                if isinstance(decl, OutDecl):
                    outputs[decl.sym] = T
                else:
                    self.sym_table[decl.sym] = T
            elif isinstance(stmt, AssignStmt):

                type_check_params(call.comb, call.pargs, self.sym_table)
                itypes, otypes = call.comb.get_type(*call.pargs)
                if len(itypes) != len(stmt.call.args):
                    raise TypeError("Mismatch in number of args")
                for arg in stmt.call.args:
                    if isinstance(arg.value, Sym) and arg.value not in self.sym_table:
                        raise TypeError(f"{arg.value} used before defined")


                if len(otypes) != len(stmt.lhss):
                    raise TypeError("Mismatch in number of args")

                for lhs, otype in zip(stmt.lhss, otypes):
                    if lhs in self.sym_table:
                        raise TypeError(f"Redefinition of {lhs}")
                    self.sym_table[lhs] = otype
            else:
                x = 1+2
                print(x)
                raise NotImplementedError(stmt)

        for sym in outputs:
            if sym not in self.sym_table:
                raise TypeError(f"{sym} never assigned!")


    def type_check(self):
        pass

Modules = {}
#from .modules import BitVectorModule, ParamModule
#
#self.modules = {'bv': BitVectorModule(), 'p': ParamModule()}


def resolve_qsym(qsym):
    if qsym.module not in Modules:
        raise ValueError("Missing module ", qsym.module)
    return Modules[qsym.module].comb_from_sym(qsym)

def resolve_expr(expr: Expr):
    if isinstance(expr.value, ASTCallExpr):
        acexpr = expr.value
        call_comb = resolve_qsym(acexpr.qsym)
        new_args = [resolve_expr(arg) for arg in acexpr.args]
        return CallExpr(call_comb, acexpr.pargs, new_args)
    return expr


def symbol_resolution(acomb: ASTCombProgram) -> CombProgram:
    from . import stdlib
    stmts = []
    for astmt in acomb.stmts:
        if isinstance(astmt, DeclStmt):
            stmt = astmt
        elif isinstance(astmt, ASTAssignStmt):
            new_exprs = [resolve_expr(rhs) for rhs in astmt.rhss]
            stmt = AssignStmt(astmt.lhss, new_exprs)
        else:
            raise ValueError()
        stmts.append(stmt)
    return CombProgram(acomb.name, stmts)


class ANON:
    @property
    def has_params(self):
        return len(self.params) > 0

    #def param_types(self):
    #    raise NotImplementedError()

    #def create_symbolic_inputs(self):
    #    return (self.sym_table[ivar.qsym].free_var(ivar.qsym) for ivar in self.inputs)

    def serialize(self):
        lines = []
        lines.append(f"Comb {self.name}")
        lines += [str(stmt) for stmt in self.stmts]
        return "\n".join(lines)

    #Only evaling for SMT
    def eval(self, *args):
        assert len(args) == len(self.inputs)
        val_table = {var.qsym:arg for arg, var in zip(args, self.inputs)}
        def get_val(arg):
            if isinstance(arg, BVValue):
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
        return tuple(val_table[var.qsym] for var in self.outputs)

    def __post_init__(self):
        pass
        #raise NotImplementedError()
        #self.params = [d.var for d in self.stmts if isinstance(d, ParamDecl)]
        #self.inputs = [d.var for d in self.stmts if isinstance(d, InDecl)]
        #self.outputs = [d.var for d in self.stmts if isinstance(d, OutDecl)]

        ##p_valid = all(isinstance(d, ParamDecl) for d in self.decls[:len(self.params)])
        ##i_valid = all(isinstance(d, InDecl) for d in self.decls[len(self.params):-len(self.outputs)])
        ##o_valid = all(isinstance(d, OutDecl) for d in self.decls[-len(self.outputs):])
        ##if not (p_valid and i_valid and o_valid):
        ##    raise TypeError("Params, then Ins, then Outs")
        #self.resolve_qualified_symbols()
        #self.type_inference()
        #self.type_check()

    #Makes sure all the QSym symbols exist (ops and types)
    def resolve_qualified_symbols(self):
        #Default Modules
        from .stdlib import BitVectorModule, IntModule
        self.modules = {'bv':BitVectorModule(), 'p':IntModule()}

        def resolve_comb(qsym):
            if qsym.module not in self.modules:
                raise ValueError("Missing module ", qsym.module)
            return self.modules[qsym.module].comb_from_sym(qsym)

        def resolve_type(qsym):
            if qsym.module not in self.modules:
                raise ValueError("Missing module ", qsym.module)
            return self.modules[qsym.module].type_from_sym(qsym)

        #Resolve Ops
        self.qsym_to_comb = {}
        self.qsym_to_type = {}
        for stmt in self.stmts:
            if isinstance(stmt, Decl):
                type_name: QSym = stmt.var.type.qsym
                self.qsym_to_type[type_name] = resolve_type(type_name)
            else:
                assert isinstance(stmt, Assign)
                comb_name = stmt.call.qsym
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
                if isinstance(pv, IntValue) and pt is not IntType:
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
                name = stmt.var.qsym
                t_name = stmt.var.type.qsym
                t_params = stmt.var.type.pargs
                if len(t_params) > 0:
                    raise NotImplementedError("Param types cannot be parametrized")
                if name in self.p_sym_table:
                    raise TypeError(f"Redefinition of {name}")
                self.p_sym_table[name] = self.qsym_to_type[t_name]()
            elif isinstance(stmt, (InDecl, OutDecl)):
                name = stmt.var.qsym
                t_name = stmt.var.type.qsym
                t_params = stmt.var.type.pargs
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
                comb = self.qsym_to_comb[stmt.call.qsym]
                if len(comb.input_types(*stmt.call.pargs)) != len(stmt.call.args):
                    raise TypeError("Mismatch in number of args")

                #Determine if this is a param_call or an arg call
                p_call = all(isinstance(arg, str) and arg in self.p_sym_table for arg in stmt.args)
                if p_call:
                    param_assigns[i] = stmt
                    #Type check the arguments
                else:
                    if not all(isinstance(arg, str) and arg in self.v_sym_table for arg in stmt.args):
                        raise ValueError(f"{stmt} has arg used before defined")
                param_check(comb.param_types, stmt.call.pargs)
                output_types = comb.output_types(*stmt.call.pargs)
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
        tc = collections.defaultdict(list)
        consts = []
        for sym, t in self.v_sym_table.items():
            tc[sym].append(t)
        for stmt in self.stmts:
            if isinstance(stmt, Assign):
                input_types = self.qsym_to_comb[stmt.call.qsym].input_types(*stmt.call.pargs)
                assert len(stmt.call.args) == len(input_types)
                for arg, t in zip(stmt.call.args, input_types):
                    if isinstance(arg, BVValue):
                        consts.append([t, TypeCall(arg.width)])
                    else:
                        tc[arg].append(t)
        print(tc)
        print(consts)
        assert 0