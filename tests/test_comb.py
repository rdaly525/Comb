from comb import program_to_comb
import pytest


padd = '''
comb test.add3
input i0 : bv.bv[16]
input i1 : bv.bv[16]
input i2 : bv.bv[16]
output o0 : bv.bv[16]
t0 = bv.add[16](i0, i1)
o0 = bv.add[16](t0, i2)


'''

pconst = '''
comb test.pconst
input i0 : bv.bv[13]
output o0 : bv.bv[13]
o0 = bv.add[13](i0, 13'h23)
'''

@pytest.mark.parametrize("p", [
    padd,
    pconst,
])
def test_round_trip(p):
    comb = program_to_comb(p)
    p1 = comb.serialize()
    comb1 = program_to_comb(p1)
    p2 = comb1.serialize()
    assert p1 == p2

@pytest.mark.parametrize("p", [
    padd,
    pconst,
])
def test_eval(p):
    comb = program_to_comb(p)
    args = comb.create_symbolic_inputs()
    res = comb.eval(*args)
    print(res)

#inc = '''
#comb test.inc
#Param N: Int
#In a: bv.bv[N]
#Out o: bv.bv[N]
#o = bv.add[N](a, [N]'h1)
#'''
#
#def test_param():
#    comb = program_to_comb(inc)
#    assert comb.has_params
#    inc1 = comb.serialize()
#    comb1 = program_to_comb(inc1)
#    inc2 = comb1.serialize()
#    assert inc1 == inc2
#
#    comb5 = comb.partial_eval(N=5)
#    args = comb.create_symbolic_inputs(N=5)
#    print(comb5.eval(*args))
#    print(comb.eval(*args, N=5))

