from comb.ast import BVType, IntValue, TypeCall
from comb.compiler import compile_program
from comb.synth import BuckSynth, verify, SolverOpts
from comb.double_synth import Strat2Synth
import pytest


import itertools as it
from comb.stdlib import GlobalModules
BV = GlobalModules['bv']
import hwtypes as ht


def test_strat2():
    BV16 = TypeCall(BVType(), [IntValue(16)])
    lhs = [BV.add[16], BV.mul[16]]
    rhs = [BV.add[16], BV.mul[16], BV.mul[16]]
    iT = [BV16 for _ in range(3)]
    oT = [BV16 for _ in range(1)]
    ss = Strat2Synth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=True, max_iters=1000, solver_name='z3')
    sols = ss.gen_all_sols(opts=opts)
    for l,r in sols:
        print("-"*80)
        print(l)
        print("->")
        print(r)

