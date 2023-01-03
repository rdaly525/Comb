from comb.compiler import compile_program
from comb.discover import discover, discover_up_to_N
from comb.ast import QSym
from comb.stdlib import BitVectorModule, GlobalModules
import pytest
import hwtypes as ht

p_or32 = '''
Comb test.id
Param N: Int 
In x0: BV[N]
In x1: BV[N]
In y0: BV[N]
In y1: BV[N]
Out z1: BV[N]
x = bv.concat[N, N](x0, x1)
y = bv.concat[N, N](y0, y1)
z = bv.mul[N*2](x, y)
z1 = bv.slice[2*N, N, 2*N](z)
'''


BV = GlobalModules['bv']
@pytest.mark.parametrize("p, N", [
    (p_or32, 2),
    #(p_or32, 16),
])
def test_discover(p, N: int):
    c1 = compile_program(p)
    op_list = [BV.add[N], BV.mul[N]]
    N_, combs = discover_up_to_N(c1[N], 8, op_list)
    for i, comb in enumerate(combs):
        print("*"*80)
        print(i)
        print(comb.serialize())



