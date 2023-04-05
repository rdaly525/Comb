from hwtypes import smt_utils as fc
from pysmt import shortcuts as smt
from pysmt.logics import QF_BV

from ..frontend.ast import Comb
from .utils import _make_list


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

    formula = fc.And([o0_ == o1_ for o0_, o1_ in zip(o0, o1)])

    not_formula = ~(formula.to_hwtypes())

    with smt.Solver(logic=logic, name=solver_name) as solver:
        solver.add_assertion(not_formula.value)
        res = solver.solve()
        if res is False:
            return None
        vals = {v.value: v.value.constant_value() for v in inputs}
        return vals
