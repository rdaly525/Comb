from comb.frontend.compiler import compile_program
from comb.synth.verify import verify

file1 = '''
Comb test.dist1
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
ab = bv.mul[N](a,b)
ac = bv.mul[N](a,c)
o = bv.add[N](ab, ac)

Comb test.dist2
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
b_p_c = bv.add[N](b, c)
o = bv.mul[N](a, b_p_c)
'''


def test_dist():
    obj1 = compile_program(file1)
    c1 = obj1.get('test', 'dist1')
    c2 = obj1.get('test', 'dist2')
    N = 16
    res = verify(c1[N], c2[N])
    assert res is None
