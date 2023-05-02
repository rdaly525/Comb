import functools
import typing as tp
from dataclasses import dataclass
import hwtypes as ht
from pysmt import shortcuts as smt

from pysmt.logics import Logic, QF_BV

from comb.frontend.ast import Type, TypeCall
from comb.synth.utils import type_to_nT, nT
import multiprocessing as mp
import timeit
import itertools as it


class IterLimitError(Exception):
    pass

class TimeoutError(Exception):
   pass

@dataclass
class SolverOpts:
    logic: Logic = QF_BV
    max_iters: int = 1000
    timeout: int = 20
    solver_name: str = "z3"
    log: bool = False
    verbose: int = 0

def timer(opts:SolverOpts):
    def _timer(f):
        @functools.wraps(f)
        def wrapped(*args, **kwargs):
            start = timeit.default_timer()
            res = f(*args, **kwargs)
            delta = round(timeit.default_timer() - start, 3)
            if isinstance(res, IterLimitError):
                k = "MAX"
            elif res is None:
                k = "UNSAT"
            else:
                k = "SAT"
            if opts.log:
                print(f"CEGIS: ({k}, {delta})", flush=True)
            return res
        return wrapped
    return _timer

def get_model(query, vars, solver_name, logic):
    model = smt.get_model(smt.And(query), solver_name=solver_name, logic=logic)
    if model:
        return {v: model.get_value(v) for v in vars}
    return False

@dataclass
class Cegis:
    query: ht.SMTBit
    E_vars: tp.Iterable['freevars']

    def cegis(self, prev_sol, opts: SolverOpts = SolverOpts()):
        if opts.verbose==2:
            show_e = True
            show_iter = True
        elif opts.verbose:
            show_e = False
            show_iter = True
        else:
            show_e = False
            show_iter = False
        #assert opts.max_iters > 0
        #print("Query Size:", smt.get_formula_size(query))
        if prev_sol is not None:
            query = self.query.value
            sol_term = smt.Bool(True)
            for var, val in prev_sol.items():
                sol_term = smt.And(sol_term, smt.EqualsOrIff(var, val))
            self.query = ht.SMTBit(smt.And(query, smt.Not(sol_term)))
        query = self.query.value
        #get exist vars:
        E_vars = set(var.value for var in self.E_vars)  # exist_vars
        A_vars = query.get_free_variables() - E_vars  # forall vars

        with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
            solver.add_assertion(smt.Bool(True))

            # Start with checking all A vals beings 0
            A_vals = {v: _int_to_pysmt(0, v.get_type()) for v in A_vars}
            solver.add_assertion(query.substitute(A_vals).simplify())
            start = timeit.default_timer()
            for i in it.count(1):
                if (timeit.default_timer()-start > opts.timeout):
                    if show_iter:
                        print("TO")
                    return IterLimitError(), opts.timeout

                if show_iter and i%10==0:
                    print(f".{i}", end='', flush=True)
                E_res = solver.solve()

                if not E_res:
                    if show_iter:
                        print("UNSAT")
                    return None, (timeit.default_timer()-start)
                else:
                    E_guess = {v: solver.get_value(v) for v in E_vars}
                    if show_e and i%100==50:
                        print_e(E_guess)
                    query_guess = query.substitute(E_guess).simplify()
                    model = smt.get_model(smt.Not(query_guess), solver_name=opts.solver_name, logic=opts.logic)
                    if model is None:
                        if show_iter:
                            print("SAT")
                        return E_guess,  (timeit.default_timer()-start)
                    else:
                        A_vals = {v: model.get_value(v) for v in A_vars}
                        solver.add_assertion(query.substitute(A_vals).simplify())


    #enum_fun takes a single solution and enumerates all 'permutations' of that solution to add to the exclude list
    def cegis_all(self, exclude_prev: bool, opts: SolverOpts = SolverOpts()):
        prev = None
        while True:
            sol, t = self.cegis(prev_sol=prev, opts=opts)
            if sol is not None:
                assert sol != prev
            if opts.log:
                if isinstance(sol, IterLimitError):
                    k = 'MAX'
                elif sol is None:
                    k = "UNSAT"
                else:
                    k = "SAT"
                print(f"CEGIS: ({k}, {round(t,3)})",flush=True)
            if isinstance(sol, IterLimitError):
                break
            if sol is None:
                break
            if exclude_prev:
                prev = sol
            yield sol, t


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
