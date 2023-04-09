import typing as tp
from dataclasses import dataclass

import hwtypes as ht
from pysmt import shortcuts as smt

from pysmt.logics import Logic, QF_BV

from comb.frontend.ast import Type, TypeCall
from comb.synth.utils import type_to_nT, nT


class IterLimitError(Exception):
    pass


@dataclass
class SolverOpts:
    logic: Logic = QF_BV
    max_iters: int = 1000
    solver_name: str = "z3"
    verbose: int = 0


@dataclass
class Cegis:
    query: ht.SMTBit
    E_vars: tp.Iterable['freevars']

    def cegis(self, opts: SolverOpts = SolverOpts(), exclude_list=[]):
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
        print("Query Size:", smt.get_formula_size(query))
        for sol in exclude_list:
            sol_term = smt.Bool(True)
            for var, val in sol.items():
                sol_term = smt.And(sol_term, smt.EqualsOrIff(var, val))
            query = smt.And(query, smt.Not(sol_term))

        #get exist vars:
        E_vars = set(var.value for var in self.E_vars)  # exist_vars
        A_vars = query.get_free_variables() - E_vars  # forall vars

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
    def cegis_all(self, opts: SolverOpts = SolverOpts(), enum_fun=None):
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
def get_var(name, T):
    #Translate to n, const
    if isinstance(T, TypeCall):
        T = type_to_nT(T)
    elif isinstance(T, int):
        T = nT(T, False)
    assert isinstance(T, nT)
    assert T.n >= 0
    key = (name, T)
    var_name = f"{name}@{T.n}"
    if T.const:
        var_name += "C"
    if key in _vars:
        return _vars[key]
    if T.n==0:
        var = ht.SMTBit(name=var_name)
    else:
        var = ht.SMTBitVector[T.n](name=var_name)
    _vars[key] = var
    return var


def smt_is_sat(f, opts: SolverOpts = SolverOpts()):
    with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
        solver.add_assertion(f)
        res = solver.solve()
        return (res is not False)

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


def print_e(e):
    print()
    for k, v in e.items():
        print(f"  {k}: {v}")
