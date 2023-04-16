import itertools
import os

import pytest

from comb import Comb
from comb.frontend.compiler import compile_program
from comb.synth.comb_encoding import CombEncoding
from comb.synth.comm_synth import set_comm
from comb.synth.const_synth import ConstDiscover
from comb.synth.pattern import SymOpts
from comb.synth.rule import Rule, RuleDatabase
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/simple.comb"
import typing as tp




def test_const_synth():
    N = 16
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    ir = [c[N] for c in obj.get_from_ns("ir")]
    maxIR = 3
    maxOp = {0:0,1:2,2:2,3:1}
    cvals = [0]
    sym_opts = SymOpts(comm=True, same_op=True, input_perm=True)
    cd = ConstDiscover(ir, maxIR, maxOp, CombEncoding, sym_opts)
    opts = SolverOpts(verbose=1, timeout=10)
    (ea_pats, const_specs), id_pats = cd.gen_all(cvals, opts)
    for cval, pats in ea_pats.items():
        print("Constant", cval)
        for pat in pats:
            print("*"*80)
            print(pat.to_comb())

    print("Identity pats")
    for pat in id_pats:
        print("*"*80)
        print(pat.to_comb())

