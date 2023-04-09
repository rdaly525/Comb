from comb.frontend.compiler import  compile_program
import pytest
import hwtypes as ht
from comb.frontend.ast import BVValue, IntValue, TypeCall

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

add_c = '''
Comb test.add_c
In i0 : BV[16]
In c0 : CBV[16]
Out o : BV[16]
t0 = bv.abs_const[16](c0)
o = bv.add[16](i0, t0)
'''

inc1 = '''
Comb test.inc1
In i0 : BV[16]
Out o : BV[16]
o = bv.add[16](i0, 16'h23)
'''

inc2 = '''
Comb test.inc2
In i0 : BV[16]
Out o : BV[16]
o = bv.add[16](i0, [16]'h23)
'''

inc3 = '''
Comb test.inc3
In i0 : BV[16]
Out o : BV[16]
o = bv.add[16](i0, [16]'h[35])
'''

p_add = '''
Comb test.padd
Param N: Int
In a: BV[N]
Out o: BV[N]
o = bv.add[N](a, a)
'''

p_add_c = '''
Comb test.p_add_c
Param N: Int
In i0 : BV[N]
In c0 : CBV[N]
Out o : BV[N]
t0 = bv.abs_const[N](c0)
o = bv.add[N](i0, t0)
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

p_concat = '''
Comb test.p_concat
Param N: Int
In a: BV[N]
Out b: BV[N+N]
b = bv.concat[N, N](a, a)
'''

p_slice = '''
Comb test.p_concat
Param N: Int
In a: BV[2*N]
Out b: BV[N]
b = bv.slice[2*N, 0, N](a)
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
    p_concat,
    p_slice,
    add_c,
    p_add_c,
])
def test_round_trip(p):
    obj = compile_program(p)
    p1 = obj.serialize()
    obj1 = compile_program(p1)
    assert obj.serialize() == obj1.serialize()
    assert str(obj) == str(obj1)
    assert hash(obj) == hash(obj1)
    assert obj == obj1

@pytest.mark.parametrize("p", [
    iadd,
    add,
    add2,
    inc1,
    inc2,
    inc3,
    add_c,
])
def test_eval(p):
    obj = compile_program(p)
    comb = list(obj.comb_dict.values())[0]
    assert not comb.has_params
    pargs = []
    args = comb.create_symbolic_inputs(*pargs, node=True)
    res = comb.eval(*args, pargs=pargs)[0]
    outT = comb.get_type()[1][0]
    if isinstance(outT, TypeCall):
        assert isinstance(res, BVValue)
    else:
        assert isinstance(res, IntValue)

@pytest.mark.parametrize("p", [
    iadd,
    add,
    add2,
    inc1,
    inc2,
    inc3,
])
def test_evaluate_sym(p):
    obj = compile_program(p)
    comb = list(obj.comb_dict.values())[0]
    assert not comb.has_params
    pargs = []
    args = comb.create_symbolic_inputs(*pargs, node=False)
    res = comb.evaluate(*args)
    assert isinstance(res, type(args[0]))


BV = ht.SMTBitVector[16]
@pytest.mark.parametrize("p, i, o", [
    (iadd, (4, 5), 18),
    (add, (BV(4), BV(5)), BV(18)),
    (add_c, (BV(4), BV(5)), BV(9)),
    (add2, (BV(4), BV(5)), BV(13)),
    (inc1, (BV(8),), BV(8+35)),
    (inc2, (BV(8),), BV(8+35)),
    (inc3, (BV(8),), BV(8+35)),
])
def test_evaluate_raw(p, i, o):
    obj = compile_program(p)
    comb = list(obj.comb_dict.values())[0]
    assert not comb.has_params
    res = comb.evaluate(*i)
    if isinstance(o, int):
        assert o == res
    else:
        assert (o == res).value.constant_value() is True


BV32 = ht.SMTBitVector[32]
BV48 = ht.SMTBitVector[48]

@pytest.mark.parametrize("p, i, o", [
    (p_add, (16, BV(4)), BV(8)),
    (p_add_c, (16, BV(4), BV(5)), BV(9)),
    (p_inc1, (16, BV(8)), BV(9)),
    (p_inc2, (16, BV(8),), BV(24)),
    (p_inc2N, (16, BV32(8),), BV32(40)),
    (p_inc2N2, (16, BV48(8),), BV48(24)),
    (p_concat, (16, BV(5),), BV32((5<<16)+5)),
    (p_slice, (16, BV32((5<<16)+5),), BV(5)),
])
def test_evaluate_raw_p(p, i, o):
    obj = compile_program(p)
    comb = list(obj.comb_dict.values())[0]
    assert comb.has_params
    res = comb.evaluate(*i)
    assert (o == res).value.constant_value() is True

    #Test partial
    comb_partial = comb.partial_eval(i[0])
    print(comb_partial.call_expr([], []))
    res = comb_partial.evaluate(*i[1:])
    assert (o == res).value.constant_value() is True

    #Test partial eval syntax
    comb_partial = comb[i[0]]
    res = comb_partial.evaluate(*i[1:])
    assert (o == res).value.constant_value() is True