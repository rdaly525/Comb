import typing as tp
from .ast import Comb, Expr, Sym, QSym, Stmt, DeclStmt, ASTCombProgram, ASTAssignStmt, ParamDecl, TypeCall, \
    IntType, InDecl, Type, OutDecl, ASTCallExpr, IntValue, _CallExpr, BoolType
from dataclasses import dataclass
from hwtypes import smt_utils as fc
import pysmt.shortcuts as smt

def _list_to_str(l):
    return ", ".join(str(l_) for l_ in l)


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


        def eval_sym(sym: Sym):
            assert sym.name in vals
            return [vals[sym.name]]
        def eval_expr(expr: Expr):
            if isinstance(expr, Sym):
                return eval_sym(expr)
            elif isinstance(expr, IntValue):
                return [expr.get_smt()]
            else:
                assert isinstance(expr, CallExpr)
                assert len(expr.pargs) == 0
                arg_vals = _flat([eval_expr(arg) for arg in expr.args])
                ret = expr.comb.eval(*arg_vals)
                if not isinstance(ret, (list, tuple)):
                    ret = [ret]
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

        def get_type(expr: Expr):
            if isinstance(expr, Sym):
                return [self.sym_table[expr]]
            elif isinstance(expr, IntValue):
                return [IntType()]
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

        f = fc.And(tc_conds)
        print(f.serialize())
        not_formula = ~(f.to_hwtypes())
        with smt.Solver(name='z3') as solver:
            solver.add_assertion(not_formula.value)
            res = solver.solve()
            if res is False:
                return
            raise TypeError(f"TC: Type check failed: \n{f.serialize()}")
Modules = {}
#from .modules import BitVectorModule, ParamModule
#
#self.modules = {'bv': BitVectorModule(), 'p': ParamModule()}


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
    from . import stdlib
    stmts = []
    for astmt in acomb.stmts:
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