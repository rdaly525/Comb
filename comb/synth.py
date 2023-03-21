import hwtypes.smt_utils as fc
import hwtypes as ht
from dataclasses import dataclass
from .ast import Comb, Type
from .ir import QSym
import typing as tp
import pysmt.shortcuts as smt
from pysmt.logics import QF_BV, Logic

from .utils import flat, type_to_N, _make_list, model_to_str


#import more_itertools as mit

class IterLimitError(Exception):
    pass

#Represnts the raw dag structure of a particular pattern
class Pattern:
    def __init__(self, comb_type, ops):
        self.comb_type = comb_type
        self.ops = ops
        self.op_names = [op.qualified_name for op in self.ops]
        self.nodes = ['In'] + list(range(len(ops))) + ['Out']
        self.edges = []

    def add_edge(self, lhs, rhs):
        assert len(lhs)==2 and len(rhs)==2
        assert lhs[0] in self.nodes
        assert rhs[0] in self.nodes
        if lhs[0] == "In":
            assert lhs[1] < len(self.comb_type[0])
        if rhs[0] == "Out":
            assert rhs[1] < len(self.comb_type[1])
        self.edges.append((lhs, rhs))

    @property
    def interior_edges(self):
        yield from (e for e in self.edges if all(isinstance(v, int) for v in (e[0][0], e[1][0])))

    @property
    def in_edges(self):
        yield from (e for e in self.edges if e[0][0]=='In')

    @property
    def out_edges(self):
        yield from (e for e in self.edges if e[1][0]=='Out')

    @property
    def op_dict(self):
        cnt = {}
        for i, op in enumerate(self.op_names):
            cnt.setdefault(op, []).append(i)
        return cnt

    def __str__(self):
        ret = ",".join([f"{i}:{op}" for i, op in enumerate(self.op_names)]) + "\n  "
        return ret + "\n  ".join(f"{l} -> {r}" for l,r in self.edges)

@dataclass
class SolverOpts:
    logic: Logic = QF_BV
    max_iters: int = 1000
    solver_name: str = "z3"
    verbose: int = 0

def smt_solve_all(f, opts: SolverOpts = SolverOpts()):
    E_vars = f.get_free_variables()
    with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
        solver.add_assertion(f)
        while solver.solve():
            sol = {v: solver.get_value(v) for v in E_vars}
            yield sol
            #Construct sol
            sol_term = smt.Bool(True)
            for var, val in sol.items():
                sol_term = smt.And(sol_term, smt.Equals(var, val))
            solver.add_assertion(smt.Not(sol_term))

def _int_to_pysmt(x: int, sort):
    if sort.is_bv_type():
        return smt.BV(x % sort.width, sort.width)
    else:
        assert sort.is_bool_type()
        return smt.Bool(bool(x))

SBV = ht.SMTBitVector
SBit = ht.SMTBit

def print_e(e):
    print()
    for k, v in e.items():
        print(f"  {k}: {v}")

def equals(var, val):
    if isinstance(val, bool):
        pass

@dataclass
class Cegis:
    query: ht.SMTBit
    E_vars: tp.Iterable['freevars']

    def cegis(self, opts: SolverOpts=SolverOpts(), exclude_list=[]):
        if opts.verbose==2:
            show_e = True
            show_iter = True
        elif opts.verbose:
            show_e = False
            show_iter = True
        else:
            show_e = False
            show_iter = False
        assert opts.max_iters > 0
        query = self.query.value

        for sol in exclude_list:
            sol_term = smt.Bool(True)
            for var, val in sol.items():
                sol_term = smt.And(sol_term, smt.EqualsOrIff(var, val))
            query = smt.And(query, smt.Not(sol_term))

        #get exist vars:
        E_vars = set(var.value for var in self.E_vars)  # forall_vars
        A_vars = query.get_free_variables() - E_vars  # exist vars

        with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
            solver.add_assertion(smt.Bool(True))

            # Start with checking all A vals beings 0
            A_vals = {v: _int_to_pysmt(0, v.get_type()) for v in A_vars}
            solver.add_assertion(query.substitute(A_vals).simplify())
            for i in range(opts.max_iters):
                if show_iter and i%10==0:
                    print(f".{i}", end='', flush=True)
                E_res = solver.solve()

                if not E_res:
                    if show_iter:
                        print("UNSAT")
                    return None
                else:
                    E_guess = {v: solver.get_value(v) for v in E_vars}
                    if show_e and i%100==50:
                        print_e(E_guess)
                    query_guess = query.substitute(E_guess).simplify()
                    model = smt.get_model(smt.Not(query_guess), solver_name=opts.solver_name, logic=opts.logic)
                    if model is None:
                        if show_iter:
                            print("SAT")
                        return E_guess
                    else:
                        A_vals = {v: model.get_value(v) for v in A_vars}
                        solver.add_assertion(query.substitute(A_vals).simplify())

            raise IterLimitError(f"Unknown result in CEGIS in {opts.max_iters} number of iterations")

    #enum_fun takes a single solution and enumerates all 'permutations' of that solution to add to the exclude list
    def cegis_all(self, opts: SolverOpts=SolverOpts(), enum_fun=None):
        exclude_list = []
        while True:
            try:
                sol = self.cegis(opts, exclude_list=exclude_list)
            except IterLimitError:
                print("MAXITER")
                break
            if sol is None:
                break
            if enum_fun is not None:
                new_exclude = list(enum_fun(sol))
                exclude_list += new_exclude
            else:
                exclude_list.append(sol)
            yield sol

_vars = {}
def get_var(name, n_or_T):
    if isinstance(n_or_T, int):
        n = n_or_T
    else:
        T = n_or_T
        n = type_to_N(T)
    assert n >= 0
    key = (name, n)
    var_name = f"{name}@{n}"
    if key in _vars:
        return _vars[key]
    if n==0:
        var = ht.SMTBit(name=var_name)
    else:
        var = ht.SMTBitVector[n](name=var_name)
    _vars[key] = var
    return var


@dataclass
class SymOpts:
    comm: bool = False
    same_op: bool = False
    input_perm: bool = False


class PatternSynth:
    def __init__(
        self,
        comb_type: tp.Tuple[tp.Iterable[Type], tp.Iterable[Type]],
        op_list: tp.List[Comb],
        const_list: tp.Tuple[int] = (),
        prefix: str = "",
        sym_opts: SymOpts = SymOpts(),
    ):
        self.comb_type = comb_type
        self.op_list = op_list
        self.const_list = const_list
        self.prefix = prefix
        self.sym_opts = sym_opts

        if len(self.const_list) > 0:
            raise NotImplementedError()
        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")
        iTs, oTs = self.comb_type

        # Structure
        input_vars = [get_var(f"{self.prefix}_In[{i}]", T) for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        output_vars = [get_var(f"{self.prefix}_Out[{i}]", T) for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{self.prefix}_OpIn[{opi}][{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{self.prefix}_OpOut[{opi}][{i}]", T) for i, T in enumerate(op_oTs)])
        self.input_vars = input_vars
        self.output_vars = output_vars
        self.op_out_vars = op_out_vars
        self.op_in_vars = op_in_vars
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)

    @property
    def P_lib(self):
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*self.op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(self.op_out_vars[i][j] == op_out_var)
        return fc.And(P_lib)

    @property
    def P_conn(self):
        raise NotImplementedError()

    @property
    def P_wfp(self):
        raise NotImplementedError()

    @property
    def P_sym_same_op(self):
        raise NotImplementedError()

    @property
    def P_sym_comm(self):
        raise NotImplementedError()

    @property
    def P_sym_input_perm(self):
        raise NotImplementedError()

    @property
    def P_sym(self):
        P_sym = []
        if self.sym_opts.comm:
            P_sym.append(self.P_sym_comm)
        if self.sym_opts.same_op:
            P_sym.append(self.P_sym_same_op)
        return fc.And(P_sym)


    def pattern_from_solved(self, sol):
        raise NotImplementedError()

    def comb_from_solved(self, sol, name):
        raise NotImplementedError()


class SpecSynth(Cegis):
    def __init__(
        self,
        spec: Comb,
        op_list: tp.List[Comb],
        pat_synth_t: tp.Type[PatternSynth],
        sym_opts: SymOpts = SymOpts(),
        const_list: tp.Tuple[int] = (),
    ):
        assert issubclass(pat_synth_t, PatternSynth)
        self.ps = pat_synth_t(spec.get_type(), op_list, const_list, sym_opts=sym_opts)
        self.spec = spec
        #Formal Spec (P_spec)
        P_spec = []
        for (i, ov) in enumerate(_make_list(self.spec.evaluate(*self.ps.input_vars))):
            P_spec.append(self.ps.output_vars[i] == ov)

        And = fc.And
        #Final query:
        #  Exists(L) Forall(V) P_wfp(L) & (P_lib & P_conn) => P_spec

        query = And([
            self.ps.P_sym,
            self.ps.P_wfp,
            fc.Implies(
                And([self.ps.P_lib, self.ps.P_conn]),
                And(P_spec)
            )
        ])
        print(query.serialize())
        E_vars = self.ps.E_vars
        super().__init__(query.to_hwtypes(), E_vars)

    # Tactic. Generate all the non-permuted solutions.
    # For each of those solutions, generate all the permutations
    def gen_all_sols(self, permutations=False, opts: SolverOpts=SolverOpts()) -> tp.List[Comb]:
        sols = list(self.cegis_all(opts))
        for i, sol in enumerate(sols):
            print(f"{i}: {model_to_str(sol)}")

        if permutations:
            sols = flat([self.ps.gen_op_permutations(sol) for sol in sols])

        combs = [self.ps.comb_from_solved(sol, name=QSym('Solved', f"v{i}")) for i, sol in enumerate(sols)]
        #if len(set(c.serialize_body() for c in combs)) != len(combs):
        #    c0 = combs[0].serialize_body()
        #    for i in range(1, len(combs)):
        #        if c0 == combs[i].serialize_body():
        #            print(f"BAD!, 0 = {i}")
        #            print(combs[0])
        #            print(combs[i])
        #            print(f"0:", sols[0])
        #            print(f"{i}:", sols[i])
        #    raise ValueError("Somehting went wrong")
        return combs


def verify(comb0: Comb, comb1: Comb, logic=QF_BV, solver_name='z3'):
    #Verify that the two interfaces are identical
    i0Ts, o0Ts = comb0.get_type()
    i1Ts, o1Ts = comb1.get_type()
    for i0, i1 in zip(i0Ts, i1Ts):
        assert i0.type == i1.type
    for o0, o1 in zip(o0Ts, o1Ts):
        assert o0.type == o1.type

    inputs = comb0.create_symbolic_inputs()
    o0 = _make_list(comb0.evaluate(*inputs))
    o1 = _make_list(comb1.evaluate(*inputs))

    formula = fc.And(o0_ == o1_ for o0_, o1_ in zip(o0, o1))

    not_formula = ~(formula.to_hwtypes())

    with smt.Solver(logic=logic, name=solver_name) as solver:
        solver.add_assertion(not_formula.value)
        res = solver.solve()
        if res is False:
            return None
        vals = {v.value: v.value.constant_value() for v in inputs}
        return vals
