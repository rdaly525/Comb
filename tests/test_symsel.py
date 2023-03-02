from comb.ast import TypeCall, BVType, IntValue
from comb.compiler import compile_program
from comb.symsel_synth import smart_iter, SymSelSynth
from comb.synth import smt_solve_all, SolverOpts
import hwtypes as ht
import os

def test_iter():
    for (l,r) in smart_iter(3,5):
        print(l, r)

def test_pysmt_solve():
    T = ht.SMTBitVector[8]
    x = T(prefix='x')
    y = T(prefix='y')
    f = (x+y == 4) & (x >= 0) & (y >= 0) & (x <= 4) & (y <= 4)
    for sol in smt_solve_all(f.value):
        x_val = sol[x.value]
        y_val = sol[y.value]
        print(x_val, y_val, flush=True)

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
        am_mul[N],
        am_add[N],
    ]
    rhs = [
        sm_obj.get('sm.mul')[N],
        sm_obj.get('sm.sub')[N],
        #sm_obj.get('sm.C')[N, 0],
        #sm_obj.get('sm.C')[N, 2**N-1],
        #sm_obj.get('sm.C')[N, 1],
    ]
    rhs[0].commutative = True
    rhs[1].commutative = True
    maxL = 2
    maxR = 2
    ss = SymSelSynth(lhs, rhs, maxL, maxR)
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    for rule in ss.gen_all(opts):
        print(rule)
