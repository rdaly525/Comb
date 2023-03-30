from comb.frontend.compiler import compile_program
from comb.synth.adj_encoding import AdjEncoding
from comb.synth.comb_encoding import CombEncoding
from comb.synth.depth_encoding import DepthEncoding
from comb.synth.pattern import SymOpts
from comb.synth.spec_synth import SpecSynth
from comb.synth.solver_utils import SolverOpts
from comb.synth.verify import verify
import pytest

# A*(B+C) == A*B + A*C

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

Comb test.add5
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
In i3 : BV[N]
In i4 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i1)
t1 = bv.add[N](i2, i3)
t2 = bv.add[N](i4, t0)
o0 = bv.add[N](t1, t2)
'''

import itertools as it
from comb.frontend.stdlib import GlobalModules
BV = GlobalModules['bv']


@pytest.mark.parametrize("pat_en_t", [
    AdjEncoding,
    #CombEncoding,
    #DepthEncoding,
])
@pytest.mark.parametrize("num_adds,comm,same_op,num_sols", [
    (1, False, False, 2),
    #(1, True, False, 1),
    #(2, False, False, 24),
    #(2, True, False, 6),
    #(2, True, True, 3),
    #(3, True, True, 2),
])
def test_add(pat_en_t, num_adds, comm, same_op, num_sols):
    N = 32
    obj = compile_program(add_file)
    spec = obj.comb_dict[f"test.add{num_adds+1}"][N]
    ops = [BV.add[N]] * num_adds
    #sym_opts = SymOpts(comm=comm, same_op=same_op, input_perm=False)
    sym_opts = SymOpts(comm=comm, same_op=same_op, input_perm=False)
    sq = SpecSynth(spec, ops, pat_en_t=pat_en_t, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=1000,
            verbose=1,
        ),
    )
    pats_ = []
    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        print(pat)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, spec)
        assert res is None
        pats_.append(pat)
    num_pats = len(pats_)
    print("SOLS:", num_pats)
    if pat_en_t is CombEncoding:
        assert num_pats >= num_sols
    else:
        assert num_pats == num_sols
        opts = SymOpts(comm=comm, same_op=same_op, input_perm=False)
        for pa, pb in it.combinations(pats_, 2):
            if pa.equal(pb, opts):
                print("8"*80)
                print(pa)
                print(pb)
            assert not pa.equal(pb, opts)
            assert not pb.equal(pa, opts)



sameop_f = '''\
Comb test.sameop
Param N: Int
In x : BV[N]
In y : BV[N]
Out o0 : BV[N]
o0 = bv.sub[N](x, y)
'''


@pytest.mark.parametrize("pat_en_t", [
    AdjEncoding,
    #CombEncoding,
    #DepthEncoding,
])
@pytest.mark.parametrize("same_op,num_sols", [
    (True, 21),
])
def test_same_op(pat_en_t, same_op, num_sols):
    N = 32
    obj = compile_program(sameop_f)
    spec = obj.comb_dict[f"test.sameop"][N]
    ops = [BV.not_[N]]*4 + [BV.sub[N]]
    sym_opts = SymOpts(comm=False, same_op=same_op, input_perm=False)
    sq = SpecSynth(spec, ops, pat_en_t=pat_en_t, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=1000,
            verbose=1,
        ),
    )
    #pats = list(pats)
    pats = list(pats)
    print("SOLS:", len(pats))
    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        print(pat)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, spec)
        assert res is None
        for patj in pats[pi+1:]:
            assert pat != patj



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
    sq = SpecSynth(spec, ops, pat_en_t=pat_synth_t, sym_opts=sym_opts)
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

