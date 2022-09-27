from comb import program_to_comb
import pytest

add = '''
Comb test.add3
In i0 : bv.bv[16]
In i1 : bv.bv[16]
Out o : bv.bv[16]
t0 = bv.add[16](i0, i1)
o = bv.add[16](t0, t0)
'''

inc = '''
Comb test.pconst
In i0 : bv.bv[13]
Out o : bv.bv[13]
o = bv.add[13](i0, 13'h23)
'''

inc2 = '''
Comb test.pconst
In i0 : bv.bv[13]
Out o : bv.bv[13]
o = bv.add[13](i0, [13]'h23)
'''

add_p = '''
Comb test.inc
Param N: p.Nat
In a: bv.bv[N]
Out o: bv.bv[N]
o = bv.add[N](a, a)
'''

inc_p = '''
Comb test.inc
Param N: p.Nat
In a: bv.bv[N]
Out o: bv.bv[foo]
o = bv.add[N](a, [N]'h1)

'''

Exist(X) ~((X+X == 2X) & (X+1 > 1))


@pytest.mark.parametrize("p", [
    add,
    inc,
    inc2,
    add_p,
    inc_p,
])
def test_round_trip(p):
    comb = program_to_comb(p)
    p1 = comb.serialize()
    print(p1)
    comb1 = program_to_comb(p1)
    p2 = comb1.serialize()
    assert p1 == p2

@pytest.mark.parametrize("p", [
    add,
    inc,
])
def test_eval(p):
    comb = program_to_comb(p)
    assert not comb.has_params
    args = comb.create_symbolic_inputs()
    res = comb.eval(*args)
    print(res)

    #comb5 = comb.partial_eval(N=5)
    #args = comb.create_symbolic_inputs(N=5)
    #print(comb5.eval(*args))
    #print(comb.eval(*args, N=5))

