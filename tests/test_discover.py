from comb.compiler import compile_program
from comb.discover import discover, discover_up_to_N
from comb.ast import QSym
from comb.stdlib import BitVectorModule, GlobalModules
from comb.synth import SynthQuery, verify
import pytest
import hwtypes as ht

pid = '''
Comb test.id
Param N: Int 
In a: BV[N]
Out o: BV[N]
o = bv.add[N](a, [N]'h1)
'''

ops = [
    'not_',
    'add',
]

BV = GlobalModules['bv']
@pytest.mark.parametrize("p, N, exp_N", [
    (pid, 3, 0),
    (pid, 4, 6),
])
def test_discover(p, N: int, exp_N: int):
    c1 = compile_program(p)
    op_list = [getattr(BV, op)[N] for op in ops]
    N_, combs = discover_up_to_N(c1[N], N, op_list, max_iters=1000)
    assert len(combs) == exp_N
    for i, comb in enumerate(combs):
        print("*"*80)
        print(i)
        print(comb.serialize())



