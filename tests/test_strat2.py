from comb.ast import BVType, IntValue, TypeCall
from comb.compiler import compile_program
from comb.synth import verify, SolverOpts
from comb.double_synth import Strat2Synth

from comb.stdlib import GlobalModules
BV = GlobalModules['bv']


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

    N = 3
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
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    cnt = 0
    for l, r in ss.gen_all_sols(opts=opts):
        assert verify(l, r) is None
        cnt += 1
        print("-"*80)
        print(l)
        print("->")
        print(r)
    assert cnt == 1

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
    ss = Strat2Synth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
    cnt = 0
    for l, r in ss.gen_all_sols(opts=opts):
        assert verify(l, r) is None
        cnt += 1
        print("-"*80)
        print(l)
        print("->")
        print(r)
    assert cnt == 1


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
    ss = Strat2Synth(
        comb_type=(iT, oT),
        lhs_op_list=lhs,
        rhs_op_list=rhs,
    )
    opts = SolverOpts(verbose=1, max_iters=400, solver_name='z3')
    cnt = 0
    for l, r in ss.gen_all_sols(opts=opts):
        assert verify(l, r) is None
        cnt += 1
        print("-"*80)
        print(l)
        print("->")
        print(r)
    assert cnt == 1