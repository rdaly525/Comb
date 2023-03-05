from comb.ast import TypeCall, BVType, IntValue
from comb.compiler import compile_program
from comb.symsel_synth import smart_iter, SymSelSynth
from comb.synth import smt_solve_all, SolverOpts
from comb.utils import bucket_combinations
import hwtypes as ht
import os

def test_iter():
    for (l,r) in smart_iter(3,5):
        print(l, r)

def test_bucket_comb():
    vals = list(range(5))
    buckets = [2, 0, 3]
    print()
    for combs in bucket_combinations(vals, buckets):
        print(combs)

from comb.double_synth import enum_rule_partitions
def test_enum_rule_partitions():
    op_list = ['A']*3+['B'] + ['C']*2
    rule_op_cnts = [dict(A=1,B=1,C=1), dict(A=2,C=1)]
    print()
    for v in enum_rule_partitions(op_list, rule_op_cnts):
        print(v)

        #Create the sets of products
        #[A,A,A,B,C,C]
        # 0 1 2 3 4 5
        #R0: (A,B,C)
        #R1: (A,A,C)

        #A: [
        #    R0:(0), R1:(1,2),
        #    R0:(1), R1:(0,2),
        #    R0:(2), R1:(0,1),
        #]
        #B: [
        #    R0: (3), R1: (),
        #]
        #C: [
        #    R0: (4), R1: (5),
        #    R0: (5), R1: (4),
        #]


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
        print("RULE")
        print(rule)
        print("ENDRULE")
