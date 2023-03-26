from comb.frontend.compiler import compile_program
from comb.synth.adj_encoding import AdjEncoding
from comb.synth.comb_encoding import CombEncoding
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
'''

import itertools as it
from comb.frontend.stdlib import GlobalModules
BV = GlobalModules['bv']


@pytest.mark.parametrize("pat_en_t", [
    AdjEncoding,
    CombEncoding,
])
@pytest.mark.parametrize("num_adds,comm,same_op,num_sols", [
    (1, False, False, 2),
    (1, True, False, 1),
    (2, False, False, 24),
    (2, True, False, 6),
    #(1, True, False, 1),
])
def test_add(pat_en_t, num_adds, comm, same_op, num_sols):
    N = 32
    obj = compile_program(add_file)
    spec = obj.comb_dict[f"test.add{num_adds+1}"][N]
    ops = list(it.repeat(BV.add[N], num_adds))
    #ops = [BV.add[N] for _ in range(3)] + [BV.sub[N] for _ in range(3)]
    #ops = list(it.repeat(BV.sub[N], 1))
    sym_opts = SymOpts(comm=comm, same_op=same_op)
    sq = SpecSynth(spec, ops, pat_en_t=pat_en_t, sym_opts=sym_opts)
    pats = sq.gen_all_sols(
        opts=SolverOpts(
            max_iters=1000,
            verbose=1,
        ),
    )
    pats = list(pats)
    print("SOLS:", len(pats))

    for pi, pat in enumerate(pats):
        print(pi, "*"*80)
        print(pat)
        combi = pat.to_comb("t", f"P{pi}")
        print(combi)
        res = verify(combi, spec)
        assert res is None
    assert len(pats) == num_sols
    assert all(pats[0] != pat for pat in pats[1:])


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

