from hwtypes import smt_utils as fc
from pysmt import shortcuts as smt
from pysmt.logics import QF_BV

from .solver_utils import SolverOpts
from ..frontend.ast import Comb
from .utils import _make_list, _to_int
from itertools import permutations

def verify(comb0: Comb, comb1: Comb, opts: SolverOpts=SolverOpts(), enum_io_order = False):
    inputs = comb0.create_symbolic_inputs()
    i0Ts, o0Ts = comb0.get_type()
    i1Ts, o1Ts = comb1.get_type()

    if enum_io_order:
        for inputs_perm in permutations(range(len(inputs))):
            inputs_reorder = [inputs[i] for i in inputs_perm]
            if any(i0T != i1T for i0T, i1T in zip([i0Ts[i] for i in inputs_perm], i1Ts)):
                continue
            o0 = _make_list(comb0.evaluate(*inputs))
            o1 = _make_list(comb1.evaluate(*inputs_reorder))

            for outputs_perm in permutations(range(len(o1))):
                o1_reorder = [o1[o] for o in outputs_perm]
                if any(o0T != o1T for o0T, o1T in zip(o0Ts, [o1Ts[o] for o in outputs_perm])):
                    continue

                formula = fc.And([o1_ == o0_ for o1_, o0_ in zip(o1_reorder, o0)])

                not_formula = ~(formula.to_hwtypes())

                with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
                    solver.add_assertion(not_formula.value)
                    res = solver.solve()
                    if res is False:
                        return None
        return res

    #Verify that the two interfaces are identical
    i1Ts, o1Ts = comb1.get_type()
    for i0, i1 in zip(i0Ts, i1Ts):
        assert i0.type == i1.type
    for o0, o1 in zip(o0Ts, o1Ts):
        assert o0.type == o1.type

    o0 = _make_list(comb0.evaluate(*inputs))
    o1 = _make_list(comb1.evaluate(*inputs))

    formula = fc.And([o0_ == o1_ for o0_, o1_ in zip(o0, o1)])

    not_formula = ~(formula.to_hwtypes())

    with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
        solver.add_assertion(not_formula.value)
        res = solver.solve()
        if res is False:
            return None
        vals = {v.value: _to_int(solver.get_value(v.value)) for v in inputs}
        return vals
