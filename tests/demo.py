from comb.compiler import compile_program
from comb.discover import discover_up_to_N
from comb.stdlib import GlobalModules

sub = '''
Comb test.sub
Param N : Int
In a : BV[N]
In b : BV[N]
Out o : BV[N]
o = bv.sub[N](a, b)
'''

inc = '''
Comb test.inc
Param N : Int
In a : BV[N]
Out o : BV[N]
o = bv.add[N](a, [N]'h1)
'''

one = '''
Comb test.one
Param N : Int
In a : BV[N]
Out o : BV[N]
o = [N]'h1
'''

bigadd = '''
Comb test.bigadd
Param N: Int
In x0 : BV[N]
In x1 : BV[N]
In y0 : BV[N]
In y1 : BV[N]
out z0 : BV[N]
out z1 : BV[N]
'''



BV = GlobalModules['bv']
width = 4
op_list = [BV.add[width]]
maxN=5

spec = compile_program(sub)
#spec = compile_program(inc)
#spec = compile_program(one)

N_, combs = discover_up_to_N(spec[width], maxN, op_list)
assert N_ > 0
for i, comb in enumerate(combs):
    print("*" * 80)
    print(i)
    print(comb.serialize())
