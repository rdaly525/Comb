import os

import pytest

from comb.frontend.compiler import compile_program
from comb.synth.comb_encoding import CombEncoding
from comb.synth.rule_discover import RulePostFilter
from comb.synth.solver_utils import SolverOpts

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/gauss.comb"

@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
])
def test_isa(pat_en_t):
    N = 4
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    ir = [obj.get(f"ir.I{i}")[N] for i in range(3)]
    isa = [obj.get(f"isa.I{i}")[N] for i in range(6)]
    assert all(v for v in isa)
    assert all(v for v in ir)
    maxIR = 3
    maxISA = 6
    lhs = ir[:maxIR]
    rhs = isa[:maxISA]
    opMaxIR = {0:2, 1:2, 2:1}
    opMaxISA = {i:1 for i in range(maxISA)}
    ss = RulePostFilter(lhs, rhs, maxIR, maxISA, pat_en_t, opMaxIR, opMaxISA)
    opts = SolverOpts(verbose=0, max_iters=50, solver_name='z3', timeout=10)
    rules = []
    for ri, rule in enumerate(ss.gen_all(opts)):
        #print("RULE", ri)
        #print(rule)
        #print("ENDRULE")
        rules.append(rule)