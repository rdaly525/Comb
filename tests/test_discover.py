from comb.compiler import compile_program
from comb.discover import discover, discover_up_to_N
from comb.ast import QSym
from comb.stdlib import BitVectorModule, GlobalModules
from comb.synth import SpecSynth, verify, SolverOpts
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
    (pid, 4, 2),
])
def test_discover(p, N: int, exp_N: int):
    obj = compile_program(p)
    c1 = list(obj.comb_dict.values())[0]
    op_list = [getattr(BV, op)[N] for op in ops]
    opts = SolverOpts(max_iters=1000, verbose=True)
    N_, combs = discover_up_to_N(c1[N], N, op_list, opts=opts)
    for i, comb in enumerate(combs):
        print("*"*80)
        print(i)
        print(comb.serialize())
    assert len(combs) == exp_N



