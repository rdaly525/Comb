from comb import parse_comb
import pytest


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

@pytest.mark.parametrize("p", [
    add,
    add2,
    inc1,
    inc2,
    inc3,
    p_add,
    p_inc1,
    p_inc2,
])
def test_round_trip(p):
    print(p)
    comb = parse_comb(p, debug=False)
    p1 = comb.serialize()
    comb1 = parse_comb(p1)
    p2 = comb1.serialize()
    assert p1 == p2

    for k, v in comb.sym_table.items():
        print(f"    {k} : {v}")


@pytest.mark.parametrize("p", [
    add,
    inc1,
    inc2,
    #inc3,
])
def test_eval(p):
    comb = parse_comb(p)
    assert not comb.has_params
    args = comb.create_symbolic_inputs()
    res = comb.eval(*args)
    print(res)


    #comb5 = comb.partial_eval(N=5)
    #args = comb.create_symbolic_inputs(N=5)
    #print(comb5.eval(*args))
    #print(comb.eval(*args, N=5))


@pytest.mark.parametrize("p", [
    p_add,
    p_inc1,
    #p_inc2,
])
def test_partial_eval(p):
    comb = parse_comb(p)
    assert not comb.has_params
    args = comb.create_symbolic_inputs()
    res = comb.eval(*args)
    print(res)

    #comb5 = comb.partial_eval(N=5)
    #args = comb.create_symbolic_inputs(N=5)
    #print(comb5.eval(*args))
    #print(comb.eval(*args, N=5))


