from comb.frontend.compiler import compile_program
from comb.synth.adj_encoding import AdjEncoding
from comb.synth.pattern import SymOpts
from comb.synth.spec_synth import SpecSynth
from comb.synth.solver_utils import SolverOpts
from comb.synth.verify import verify
import pytest


file1 = '''
Comb test.dist1
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
ab = bv.mul[N](a,b)
ac = bv.mul[N](a,c)
o = bv.add[N](ab, ac)

Comb test.dist2
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
b_p_c = bv.add[N](b, c)
o = bv.mul[N](a, b_p_c)
'''

# A*(B+C) == A*B + A*C
def test_dist():
    obj1 = compile_program(file1)
    c1 = obj1.comb_dict['test.dist1']
    c2 = obj1.comb_dict['test.dist2']
    N = 16
    res = verify(c1[N], c2[N])
    assert res is None



add_file = '''
Comb test.add2
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
Out o0 : BV[N]
o0 = bv.add[N](i0, i1)

Comb test.sub2
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
Out o0 : BV[N]
o0 = bv.sub[N](i0, i1)

Comb test.add3
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i1)
o0 = bv.add[N](i2, t0)

Comb test.add4
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
In i3 : BV[N]
Out o0 : BV[N]
t1 = bv.add[N](i2, i3)
t0 = bv.add[N](i0, i1)
o0 = bv.add[N](t0, t1)
'''

import itertools as it
from comb.frontend.stdlib import GlobalModules
BV = GlobalModules['bv']

@pytest.mark.parametrize("p,num_adds,num_sols", [
    #('add2', 1, 1),
    ('add3', 2, 3),
    #('add4', 3, 18),
])
@pytest.mark.parametrize("pat_synth_t", [
    AdjEncoding,
    #CombSynth,
])
def test_add(p, num_adds, num_sols, pat_synth_t):
    N = 32
    obj = compile_program(add_file)
    spec = obj.comb_dict[f"test.{p}"][N]
    ops = list(it.repeat(BV.add[N], num_adds))
    #ops = [BV.add[N] for _ in range(3)] + [BV.sub[N] for _ in range(3)]
    #ops = list(it.repeat(BV.sub[N], 1))
    sym_opts = SymOpts(comm=False, same_op=False)
    sq = SpecSynth(spec, ops, pat_synth_t=pat_synth_t, sym_opts=sym_opts)
    combs = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=1000,
            verbose=1,
        ),
    )
    combs = list(combs)
    print("SOLS:", len(combs))

    for comb_sol in combs:
        print(comb_sol)
        #res = verify(comb_sol, comb)
        #assert res is None
    assert len(combs) == num_sols


sub_file = '''
Comb test.add1
Param N: Int
In x: BV[N]
Out z: BV[N]
z = bv.add[N](x, [N]'b1)

Comb test.sub
Param N: Int
In x: BV[N]
In y: BV[N]
Out z: BV[N]
t0 = test.add1[N](x)
t1 = test.add1[N](y)
z = bv.mul[N](t0, t1)
'''

@pytest.mark.parametrize("pat_synth_t", [
    AdjEncoding,
    #CombSynth,
])
def test_op_sym(pat_synth_t):
    N = 32
    obj = compile_program(sub_file)
    spec = obj.comb_dict[f"test.sub"][N]
    ops = [BV.not_[N] for _ in range(2)] + [BV.mul[N]]
    sym_opts = SymOpts(comm=False, same_op=True)
    sq = SpecSynth(spec, ops, pat_synth_t=pat_synth_t, sym_opts=sym_opts)
    combs = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=1000,
            verbose=1,
        ),
    )
    combs = list(combs)
    print("SOLS:", len(combs))
    for comb_sol in combs:
        print(comb_sol)
        #res = verify(comb_sol, comb)
        #assert res is None
    assert len(combs) == 2

