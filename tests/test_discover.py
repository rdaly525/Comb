from comb import program_to_comb, discover, discover_up_to_N
from comb.comb import QSym
from comb.modules import Base
from comb.synth import SynthQuery, verify
import pytest
import hwtypes as ht

pid = '''
comb test.id
Param N: p.Int
In a: bv.bv[N]
Out o: bv.bv[N]
o = bv.add[N](a, [N]'h4)
'''

pid = '''
comb test.id
input a : bv.bv[4]
output o : bv.bv[4]
o = bv.add[4](a, 4'h1)
'''


ops = [
    #'identity',
    'not_',
    #'neg',
    #'mul',
    'add',
    #'sub',
]

@pytest.mark.parametrize("p, N", [
    (pid, 8),
])
def test_discover(p, N: int):
    c1 = program_to_comb(p)
    op_list = [QSym('bv', op, (4,)) for op in ops]
    N_, combs = discover_up_to_N(c1, N, op_list)
    for i, comb in enumerate(combs):
        print("*"*80)
        print(i)
        print(comb.serialize())


