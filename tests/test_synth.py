from comb import compile_comb
from comb.ast import QSym, IntValue
from comb.ir import CallExpr
from comb.stdlib import BitVectorModule
from comb.synth import SynthQuery, verify
import pytest
import hwtypes as ht

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
import itertools as it
import comb.stdlib as std
bvadd16 = CallExpr(std.BVAdd(), IntValue(16))
@pytest.mark.parametrize("p,ops,num_sols", [
    (padd2, tuple(it.repeat(bvadd16, 1)), 2),
    (padd3, tuple(it.repeat(bvadd16, 2)), 12),
    (padd4, tuple(it.repeat(bvadd16, 3)), 144),
])
def test_add(p, ops, num_sols):
    comb = compile_comb(p)

    sq = SynthQuery(comb, ops, loc_type_int=False)
    combs = sq.gen_all_sols(logic=None, maxloops=1000, permutations=True, verbose=False)
    assert len(combs) == num_sols


ab_p_ac = '''
comb test.sub
input a : bv.bv[8]
input b : bv.bv[8]
input c : bv.bv[8]
output o : bv.bv[8]
ab = bv.mul[8](a,b)
ac = bv.mul[8](a,c)
o = bv.add[8](ab, ac)
'''

a_bpc = '''
comb test.sub
input a : bv.bv[8]
input b : bv.bv[8]
input c : bv.bv[8]
output o : bv.bv[8]
b_p_c = bv.add[8](b, c)
o = bv.mul[8](a, b_p_c)
'''

# A*(B+C) == A*B + A*C
def test_dist():
    c1 = compile_comb(ab_p_ac)
    c2 = compile_comb(a_bpc)
    res = verify(c1, c2)
    assert res is None