from comb.frontend.ast import BVType, IntValue, TypeCall
from comb.frontend.compiler import compile_program
from comb.synth.adj_encoding import AdjEncoding
from comb.synth.comb_encoding import CombEncoding
from comb.synth.depth_encoding import DepthEncoding
from comb.synth.pattern import SymOpts
from comb.synth.solver_utils import SolverOpts
from comb.synth.utils import nT
from comb.synth.verify import verify as synth_verify
from comb.synth.rule_synth import RuleSynth

from comb.frontend.stdlib import GlobalModules
BV = GlobalModules['bv']
import pytest

def verify(ss, opts, gold, debug=False):
    cnt = 0
    for l, r in ss.gen_all_sols(opts=opts):
        assert synth_verify(l, r) is None
        cnt += 1
        if debug:
            print("-" * 80)
            print(l)
            print("->")
            print(r)
    assert cnt == gold

@pytest.mark.parametrize("pat_en_t", [
    AdjEncoding,
    #CombEncoding,
    #DepthEncoding,
])
@pytest.mark.parametrize("num_adds, comm, same_op, input_perm, num_sols", [
    #(1, False, False, False, 4),
    #(1, True, False, False, 1),
    #(1, False, True, False, 4),
    #(1, False, False, True, 2),
    #(1, True, True, True, 1),
    #(1, False, False, False, 24*24),
    #(2, False, False, False, 24),
    #(2, False, False, False, 24**2),
    #(2, True, False, False, 6**2),
    #(2, True, True, False, 3**2),
    (2, True, True, True, 1),
    #(3, True, True, True, 2),
    #(True, True, True, 12),
    #(True, True, True, 1),
    #(False, False, 24),
    #(True, False, 6),
])
def test_add(pat_en_t, num_adds, comm, same_op, input_perm, num_sols):
    N = 16
    #Synthesize Distributive rule for Multiplication
    lhs = [BV.add[N]]*num_adds
    rhs = [BV.add[N]]*num_adds
    iT = [N]*(num_adds+1)
    oT = [N]
    sym_opts = SymOpts(comm=comm, same_op=same_op, input_perm=input_perm)
    ss = RuleSynth(
        iT,
        oT,
        lhs_op_list=lhs,
        rhs_op_list=rhs,
        pat_en_t=pat_en_t,
        sym_opts=sym_opts
    )
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    rules = ss.gen_all_sols(opts=opts)
    rules_ = []
    for i, (l, r) in enumerate(rules):
        print(i)
        combl = l.to_comb('R', f"L{i}")
        combr = r.to_comb('R', f"R{i}")
        assert synth_verify(combl, combr) is None
        print("-" * 80)
        print(combl)
        print("->")
        print(combr)
        rules_.append((l,r))
    num_rules = len(rules_)
    assert num_rules == num_sols


@pytest.mark.parametrize("pat_en_t", [
    AdjEncoding,
    #CombEncoding,
    #DepthEncoding,
])
@pytest.mark.parametrize("comm, same_op, input_perm, num_sols", [
    #(False, False, False, 8),
    (False, True, True, 2),
])
def test_addsub(pat_en_t, comm, same_op, input_perm, num_sols):
    N = 16
    #Synthesize Distributive rule for Multiplication
    lhs = [BV.add[N]]
    #lhs = [BV.add[N], BV.sub[N], BV.const[N, 1], BV.not_[N]]
    rhs = [BV.add[N], BV.sub[N], BV.const[N, 1], BV.not_[N]]
    iT = [nT(N,False)]*2
    oT = [nT(N,False)]
    sym_opts = SymOpts(comm=comm, same_op=same_op, input_perm=input_perm)
    ss = RuleSynth(
        iT,
        oT,
        lhs_op_list=lhs,
        rhs_op_list=rhs,
        pat_en_t=pat_en_t,
        sym_opts=sym_opts
    )
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    rules = ss.gen_all_sols(opts=opts)
    rules_ = []
    for i, (l, r) in enumerate(rules):
        print(i)
        combl = l.to_comb('R', f"L{i}")
        combr = r.to_comb('R', f"R{i}")
        assert synth_verify(combl, combr) is None
        print("-" * 80)
        print(combl)
        print("->")
        print(combr)
        rules_.append((l,r))
    num_rules = len(rules_)
    assert num_rules == num_sols

Cprog = '''
Comb c.const
Param N: Int
Param val: Int
Out o: BV[N]
o = bv.const[N](val)
'''
def test_foo():
    obj = compile_program(Cprog)
    C = list(obj.comb_dict.values())[0]

    N = 3
    BVN = TypeCall(BVType(), [IntValue(N)])

    #Synthesize a subtract rule
    lhs = [BV.sub[N]]
    rhs = [BV.add[N], BV.add[N], BV.not_[N], C[N, 1]]
    iT = [BVN for _ in range(2)]
    oT = [BVN for _ in range(1)]
    ss = RuleSynth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')

    #3 solitions currently because of (A+B)+C, (A+C)+B, (B+C)+A
    #   TODO Think about how to cull these cases
    #   Idea: What If I had an AddN primitive somehow
    gold = 3
    verify(ss, opts, gold, debug=True)


prog_iswap = '''
Comb u.t1
Param N: Int
In a: BV[N]
In b: BV[N]
In c: BV[N]
Out o: BV[N]
t0 = bv.and_[N](a, b)
t1 = bv.mul[N](a, c)
o = bv.add[N](t0, t1)
'''
def test_iswap():
    obj = compile_program(prog_iswap)
    spec = list(obj.comb_dict.values())[0]

    N = 3
    BVN = TypeCall(BVType(), [IntValue(N)])
    assert N > 2
    #Synthesize Distributive rule for Multiplication
    rhs = [spec[N]]
    lhs = [BV.add[N], BV.mul[N], BV.and_[N]]
    iT = [BVN for _ in range(3)]
    oT = [BVN for _ in range(1)]
    ss = RuleSynth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    verify(ss, opts, 1, debug=True)


prog = '''
Comb u.t1
Param N: Int
In a: BV[N]
In b: BV[N]
Out o: BV[N]
t0 = bv.sub[N](a, b)
t1 = bv.mul[N](b, b)
o = bv.and_[N](t0, t1)
'''
def test_dag():
    obj = compile_program(prog)
    spec = list(obj.comb_dict.values())[0]

    N = 3
    BVN = TypeCall(BVType(), [IntValue(N)])
    assert N > 2

    rhs = [spec[N]]
    lhs = [BV.sub[N], BV.mul[N], BV.and_[N]]
    iT = [BVN for _ in range(2)]
    oT = [BVN for _ in range(1)]
    ss = RuleSynth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=400, solver_name='z3')
    verify(ss, opts, 1, debug=True)

#def test_foosub():
#    N = 3
#    BVN = TypeCall(BVType(), [IntValue(N)])
#
#    lhs = [BV.add[N]]
#    rhs = [BV.sub[N]]*3
#    iT = [BVN for _ in range(2)]
#
#    oT = [BVN for _ in range(1)]
#    ss = RuleSynth(
#        comb_type=(iT, oT),
#        lhs_op_list=lhs,
#        rhs_op_list=rhs,
#    )
#    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
#    verify(ss, opts, 1, debug=True)
