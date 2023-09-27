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


#Note: I know that each spec is completely commutative about all inputs
#I can therefor test the input_perm symmetry here.
@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
    #AdjEncoding,
    #DepthEncoding,
])
@pytest.mark.parametrize("num_adds,comm,same_op,iperm,num_sols", [
    (1, False, False, False, 2),
    (1, False, True, False, 2),
    (1, True, False, False, 1),
    (1, True, True, False, 1),
    (1, False, False, True, 1),
    (1, False, True, True, 1),
    (1, True, False, True, 1),
    (1, True, True, True, 1),
    (2, False, False, False, 24),
    (2, True, False, False, 6),
    (2, True, True, False, 3),
    (2, True, True, True, 1),
    (3, True, True, False, 18),
    (3, True, True, True, 2),
])
def test_add(pat_en_t, num_adds, comm, same_op, iperm, num_sols):
    N = 32
    obj = compile_program(add_file)
    spec = obj.get("test",f"add{num_adds+1}")[N]
    ops = [BV.add[N]] * num_adds
    sym_opts = SymOpts(comm=comm, same_op=same_op, input_perm=iperm)
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
        assert num_pats == num_sols
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
    CombEncoding,
    DepthEncoding,
])
@pytest.mark.parametrize("same_op,num_sols", [
    (True, 9),
])
def test_same_op(pat_en_t, same_op, num_sols):
    N = 4
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
    num_pats = len(pats)
    print("SOLS:", num_pats)
    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, spec)
        assert res is None
    if pat_en_t is CombEncoding:
        assert num_pats == 21
    else:
        assert num_pats == num_sols
        opts = SymOpts(comm=False, same_op=same_op, input_perm=False)
        for pa, pb in it.combinations(pats, 2):
            if pa.equal(pb, opts):
                print("8"*80)
                print(pa)
                print(pb)
            assert not pa.equal(pb, opts)
            assert not pb.equal(pa, opts)


c_fma_obj = '''\
Comb test.c_fma
Param N : Int
In a : BV[N] 
In b : BV[N]
In c : CBV[N]
Out o : BV[N]
t0 = bv.abs_const[N](c)
t1 = bv.mul[N](a, b)
t2 = bv.add[N](t1, t0)
o = t2
'''

@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
    #AdjEncoding,
    #DepthEncoding,
])
def test_c_fma(pat_en_t):
    N = 16
    obj = compile_program(c_fma_obj)
    fma = obj.comb_dict[f"test.c_fma"][N]
    ops = [BV.abs_const[N], BV.add[N], BV.mul[N]]
    sym_opts = SymOpts(False, False, False)
    sq = SpecSynth(fma, ops, pat_en_t=pat_en_t, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=2000,
            verbose=1,
        ),
    )
    pats = list(pats)
    num_pats = len(pats)
    print("SOLS:", num_pats)
    if pat_en_t is CombEncoding:
        assert num_pats == 8
    else:
        assert num_pats == 4
    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, fma)
        assert res is None







fa_f = '''\
Comb test.fa
In ci : BV[1] 
In a : BV[1]
In b : BV[1]
Out co : BV[1]
Out s : BV[1]
a_xor_b = bv.xor[1](a, b)
s = bv.xor[1](a_xor_b, ci)
a_and_b = bv.and_[1](a, b)
t = bv.and_[1](ci, a_xor_b)
co = bv.or_[1](t, a_and_b)

Comb test.orand
In a : BV[1] 
In b : BV[1]
In c : BV[1]
In d : BV[1]
Out o : BV[1]
t0 = bv.and_[1](a, b)
t1 = bv.and_[1](c, d)
o = bv.or_[1](t0, t1)
'''



import hwtypes as ht
@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
    #AdjEncoding,
    #DepthEncoding,
])
def _test_fulladder(pat_en_t):
    N = 1
    obj = compile_program(fa_f)
    fa = obj.comb_dict[f"test.fa"]
    orand = obj.comb_dict[f"test.orand"]
    one, zero = ht.SMTBitVector[1](1), ht.SMTBitVector[1](0)
    print(fa.evaluate(one, one, one))
    print(fa.evaluate(one, zero, one))
    ops = [BV.xor[N]]*2 + [BV.and_[N]]*2 + [BV.or_[N]]
    #ops = [BV.xor[N]]*2 + [orand]
    sym_opts = SymOpts(comm=True, same_op=False, input_perm=False)
    sym_opts = SymOpts(comm=True, same_op=True, input_perm=False)
    sq = SpecSynth(fa, ops, pat_en_t=pat_en_t, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=2000,
            verbose=1,
        ),
    )
    pats = list(pats)
    num_pats = len(pats)
    print("SOLS:", num_pats)
    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, fa)
        assert res is None


#Bug where sub_sub does not equal the right thing
bad = '''
# const
Comb bad.id2
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
Out o : BV[N]
o = i1
'''

def test_sub_sub():
    N = 16
    obj = compile_program(bad)
    spec = obj.get("bad", 'id2')[N]
    ops = [BV.sub[N]]*2
    sym_opts = SymOpts(comm=True, same_op=True, input_perm=True)
    sq = SpecSynth(spec, ops, pat_en_t=CombEncoding, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            timeout=10,
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
    assert num_pats == 1