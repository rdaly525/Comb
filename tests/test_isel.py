from comb.ast import BVType, IntValue, TypeCall
from comb.compiler import compile_program
from comb.synth import verify as synth_verify, SolverOpts
from comb.discover import discover_strat2
from comb.double_synth import Strat2Synth

from comb.stdlib import GlobalModules
BV = GlobalModules['bv']

#Need to figure out how to load
import os
dir_path = os.path.dirname(os.path.realpath(__file__))

am_file = f"{dir_path}/combs/addmul.comb"
sm_file = f"{dir_path}/combs/submul.comb"



def test_foo():
    with open(am_file, 'r') as f:
        am_obj = compile_program(f.read())
    with open(sm_file, 'r') as f:
        sm_obj = compile_program(f.read())

    N = 3

    am_add = am_obj.get('am.add')
    am_add.commutative = True
    am_mul = am_obj.get('am.mul')
    am_mul.commutative = True
    lhs = [
        am_add[N],
        am_mul[N],
    ]
    rhs = [
        sm_obj.get('sm.sub')[N],
        sm_obj.get('sm.mul')[N],
        sm_obj.get('sm.C')[N, 0],
        sm_obj.get('sm.C')[N, 2**N-1],
        sm_obj.get('sm.C')[N, 1],
    ]
    rhs[0].commutative = True
    rhs[1].commutative = True

    #A Core Idea that Pat Liked:
    #      If your solution space is large and riddled with semantically equivelent solutions,
    #      it is better to constrain that space to produce a single canonical solution

    #  How to Simplify the enumeration
    #  Ideas:
    #  Once you have a rule, should not search for any rule of the same semantics that is guarneteed to be higher cost.
    #  There is probably some cool idea to use existing rules to simplify the search space.
    #  I could easily enumerate all the graphs given a rewrite rule and the constraints.
    #       This could actually be amazing.
    #       Lets say you start off with 2 rewrite rules and you just found a third
    #           I can construct new rules based on that third rule and adding sides of the first two rules.
    #       Each new graph is simply a new solution and can therefor be excluded.


    #       I really need to read that paper again which does thing to leverage existing properties.
    #
    rI = range(2,3)
    rO = range(1,2)
    rL = range(1,2)
    rR = range(1,4)
    ranges = rI, rO, rL, rR
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    for i, (l, r) in enumerate(discover_strat2(lhs, rhs, ranges, N, opts)):
        assert synth_verify(l, r) is None
        print(f"{i}-" * 40)
        print(l)
        print("->")
        print(r)
