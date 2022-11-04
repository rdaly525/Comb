from comb.compiler import  compile_program
import pytest

from comb.ast import Obj, BVValue

iadd = '''
Comb test.iadd
In i0 : Int
In i1 : Int
Out o : Int
t0 = i.add(i0, i1)
o = i.add(t0, t0)
'''

add = '''
Comb test.add
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0 = bv.add[16](i0, i1)
o = bv.add[16](t0, t0)
'''

add2 = '''
Comb test.add
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0, t1 = bv.add[16](i0, i1), i0
o = bv.add[16](t0, t1)
'''

inc1 = '''
Comb test.inc1
In i0 : BV[13]
Out o : BV[13]
o = bv.add[13](i0, 13'h23)
'''

inc2 = '''
Comb test.inc2
In i0 : BV[13]
Out o : BV[13]
o = bv.add[13](i0, [13]'h23)
'''

inc3 = '''
Comb test.inc3
In i0 : BV[13]
Out o : BV[13]
o = bv.add[13](i0, [13]'h[23])
'''

p_add = '''
Comb test.padd
Param N: Int
In a: BV[N]
Out o: BV[N]
o = bv.add[N](a, a)
'''

p_inc1 = '''
Comb test.p_inc1
Param N: Int 
In a: BV[N]
Out o: BV[N]
o = bv.add[N](a, [N]'h1)
'''

p_inc2 = '''
Comb test.p_inc2
Param N: Int 
In a: BV[N]
Out o: BV[N]
o = bv.add[N](a, [N]'h[N])
'''

p_inc2N = '''
Comb test.p_inc2N
Param N: Int 
N2 = i.mul(N, 2)
In a: BV[N2]
Out o: BV[N2]
o = bv.add[N2](a, [N2]'h[N2])
'''

p_inc2N2 = '''
Comb test.p_inc2N2
Param N: Int 
In a: BV[3*N]
Out o: BV[N+N+N]
o = bv.add[N + 2*N](a, [3*N]'h[N])
'''

@pytest.mark.parametrize("p", [
    iadd,
    add,
    add2,
    inc1,
    inc2,
    inc3,
    p_add,
    p_inc1,
    p_inc2,
    p_inc2N,
    p_inc2N2,
])
def test_round_trip(p):
    comb = compile_program(p, debug=False)
    p1 = comb.serialize()
    comb1 = compile_program(p1)
    assert comb.serialize() == comb1.serialize()
    assert str(comb) == str(comb1)
    assert hash(comb) == hash(comb1)
    assert comb == comb1

@pytest.mark.parametrize("p", [
    #iadd,
    add,
    add2,
    inc1,
    inc2,
    inc3,
])
def test_eval(p):
    comb = compile_program(p)
    assert not comb.has_params
    args = comb.create_symbolic_inputs()
    res = comb.eval([], args)
    assert isinstance(res, BVValue)

@pytest.mark.parametrize("p", [
    p_add,
    p_inc1,
    p_inc2,
    p_inc2N,
    p_inc2N2,
])
def test_partial_eval(p):
    comb = compile_program(p)
    assert comb.has_params
    args = comb.create_symbolic_inputs()
    res = comb.eval(*args)
    print(res)

p_obj0 = \
'''
Comb test.t1
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0 = bv.add[16](i0, i1)
o = bv.add[16](t0, t0)

Comb test.t0
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0 = test.t1(i0, i1)
o = bv.add[16](t0, t0)
'''

@pytest.mark.parametrize("p", [
    p_obj0,
])
def test_obj(p):
    obj: Obj = compile_program(p, comb=False, debug=False)
