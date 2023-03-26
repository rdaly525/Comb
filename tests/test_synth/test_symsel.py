from comb.frontend.compiler import compile_program
from comb.frontend.symsel_synth import smart_iter, SymSelSynth
from comb.synth.solver_utils import SolverOpts, smt_solve_all
from comb.synth.utils import bucket_combinations
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

from comb.synth.rule_synth import enum_rule_partitions
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

    N = 8
    am_add = am_obj.get('am.add')
    am_add.commutative = True
    am_mul = am_obj.get('am.mul')
    am_mul.commutative = True
    am_add1 = am_obj.get('am.add1')
    sm_sub = sm_obj.get('sm.sub')
    sm_sub.commutative = True
    sm_mul = sm_obj.get('sm.mul')
    sm_C = sm_obj.get('sm.C')
    sm_mul.commutative = True


    lhs = [
        am_add1[N],
    ]
    rhs = [
        #sm_mul[N],
        sm_sub[N],
        #sm_sub[N],
        #sm_C[N, 0],
        sm_C[N, 2**N-1],
        #sm_C[N, 1],
    ]
    maxL = 1
    maxR = 4
    ss = SymSelSynth(lhs, rhs, maxL, maxR)
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    rules = []
    for ri, rule in enumerate(ss.gen_all(opts)):
        print("RULE", ri)
        print(rule)
        print("ENDRULE")
        rules.append(rule)
    print("-"*80)
    print("-"*80)
    print("-"*80)
    for ri, rule in enumerate(rules):
        print("RULE", ri)
        print(rule)
        print("ENDRULE")
