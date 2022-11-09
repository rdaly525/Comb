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
    #'identity',
    'not_',
    #'neg',
    #'mul',
    'add',
    #'sub',
]

BV = GlobalModules['bv']
@pytest.mark.parametrize("p, N", [
    (pid, 4),
    (pid, 2),
])
def test_discover(p, N: int):
    c1 = compile_program(p)
    op_list = [getattr(BV, op)[N] for op in ops]
    N_, combs = discover_up_to_N(c1[N], N, op_list)
    assert len(combs) == 6
    for i, comb in enumerate(combs):
        print("*"*80)
        print(i)
        print(comb.serialize())
