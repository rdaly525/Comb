from comb.compiler import compile_program
from comb.synth import SynthQuery, verify
import pytest


ab_p_ac = '''
Comb test.sub
In a : BV[8]
In b : BV[8]
In c : BV[8]
Out o : BV[8]
ab = bv.mul[8](a,b)
ac = bv.mul[8](a,c)
o = bv.add[8](ab, ac)
'''

a_bpc = '''
Comb test.sub
In a : BV[8]
In b : BV[8]
In c : BV[8]
Out o : BV[8]
b_p_c = bv.add[8](b, c)
o = bv.mul[8](a, b_p_c)
'''

# A*(B+C) == A*B + A*C
def test_dist():
    c1 = compile_program(ab_p_ac)
    c2 = compile_program(a_bpc)
    res = verify(c1, c2)
    assert res is None



padd2 = '''
Comb test.add2
In i0 : BV[16]
In i1 : BV[16]
Out o0 : BV[16]
o0 = bv.add[16](i0, i1)
'''

padd3 = '''
Comb test.add3
In i0 : BV[16]
In i1 : BV[16]
In i2 : BV[16]
Out o0 : BV[16]
t0 = bv.add[16](i0, i1)
o0 = bv.add[16](i2, t0)
'''

padd4 = '''
Comb test.add4
In i0 : BV[16]
In i1 : BV[16]
In i2 : BV[16]
In i3 : BV[16]
Out o0 : BV[16]
t1 = bv.add[16](i2, i3)
t0 = bv.add[16](i0, i1)
o0 = bv.add[16](t0, t1)
'''

import itertools as it
from comb.stdlib import GlobalModules
BV = GlobalModules['bv']

@pytest.mark.parametrize("p,ops,num_sols", [
    (padd2, tuple(it.repeat(BV.add[16], 1)), 2),
    (padd3, tuple(it.repeat(BV.add[16], 2)), 12),
    #(padd4, tuple(it.repeat(BV.add[16], 3)), 144),
])
def test_add(p, ops, num_sols):
    comb = compile_program(p)
    sq = SynthQuery(comb, ops, loc_type_int=False)
    comb_sols = sq.gen_all_sols(logic=None, maxloops=1000, permutations=True, verbose=False)
    assert len(comb_sols) == num_sols
    for comb_sol in comb_sols:
        res = verify(comb_sol, comb)
        assert res is None
