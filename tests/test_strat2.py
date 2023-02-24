from comb.ast import BVType, IntValue, TypeCall
from comb.compiler import compile_program
from comb.synth import BuckSynth, verify, SolverOpts
from comb.double_synth import Strat2Synth
import pytest


import itertools as it
from comb.stdlib import GlobalModules
BV = GlobalModules['bv']
import hwtypes as ht


#Issues:
#   If the inputs are the same type, there are different permutation issues
#       #It would be safe to add strict argument ordering for inputs of the same type
#       #I could figure out how to enumerate all the different input orderings
#   The code line number order is an issue.
#       Either I need to come up with a encoding of the canonical topological sort 
#           (Seems kind of impossible)
#           Maybe not... Could be a cool presentation if I figure it out
#           I could encode indicator for first line and last line
#           Perhaps there is a 2D (or ND) location grid which ops could be mapped to
#           Then I could encoder an indicator for the second dep, and third, etc... ??
#       OR Just enumerate all other topological sorts and add them as solution constraints
#           I suspect doing the exercise of enumerating all topological sorts would work


Cprog = '''
Comb c.const
Param N: Int
Param val: Int
Out o: BV[N]
o = bv.const[N](val)
'''


def test_strat2():
    obj = compile_program(Cprog)
    C = list(obj.comb_dict.values())[0]

    N = 2
    BVN = TypeCall(BVType(), [IntValue(N)])

    #Synthesize a subtract rule
    #lhs = [BV.sub[N]]
    #rhs = [BV.add[N], BV.add[N], BV.not_[N], C[N, 1]]
    #iT = [BVN for _ in range(2)]

    #Synthesize Distributive rule for Multiplication
    lhs = [BV.add[N], BV.mul[N]]
    rhs = [BV.add[N]] + [BV.mul[N]]*2
    iT = [BVN for _ in range(3)]

    oT = [BVN for _ in range(1)]
    ss = Strat2Synth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=400, solver_name='z3')
    for l, r in ss.gen_all_sols(opts=opts):
        print("-"*80)
        print(l)
        print("->")
        print(r)

