import itertools
import os

import pytest

from comb import Comb
from comb.frontend.compiler import compile_program
from comb.synth.comb_encoding import CombEncoding
from comb.synth.comm_synth import set_comm
from comb.synth.pattern import SymOpts
from comb.synth.rule import Rule, RuleDatabase
from comb.synth.rule_discover import RulePostFilter
from comb.synth.solver_utils import SolverOpts

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/gauss.comb"
import typing as tp


from timeit import default_timer as time

@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
])
def test_isa(pat_en_t):
    N = 4
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    ir = [obj.get(f"ir.I{i}")[N] for i in range(3)]
    isa = [obj.get(f"isa.I{i}")[N] for i in range(6)]
    for op in [*ir, *isa]:
        set_comm(op)
    for i in [1,2]:
        assert ir[i].commutative
        assert isa[i].commutative

    opts = SolverOpts(verbose=0, max_iters=2000, solver_name='z3', timeout=10, log=True)
    maxIR = 3
    maxISA = 2
    lhs = ir
    rhs = isa
    opMaxIR = {0:2, 1:2, 2:1}
    opMaxISA = {0:2, 1:1, 2:1, 3:1, 4:1, 5:1}
    tot = {}
    #for c, so, ip in itertools.product((1, 0), repeat=3):
    #for c, so, ip in ((1,1,1),):
    for c, so, ip in ((1,1,1),):
        print(f"\nSYM: ({c},{so},{ip})")
        sym_opts = SymOpts(comm=c, same_op=so, input_perm=ip)

        start_time = time()
        ss = RulePostFilter(
            lhs,
            rhs,
            maxIR,
            maxISA,
            pat_en_t,
            sym_opts,
            opMaxIR,
            opMaxISA
        )
        db = RuleDatabase()
        for ri, rule in enumerate(ss.gen_all(opts)):
            #print("RULE", ri)
            #print(rule)
            #print("ENDRULE")
            db.add_rule(rule)
        gen_time = time()
        pre_rules = len(db)
        db.post_filter()
        post_time = time()
        gen_delta = round(gen_time - start_time, 4)
        post_delta = round(post_time - gen_time, 4)
        print(f"PRE: ({pre_rules}, {gen_delta})")
        print(f"POST: ({len(db)}, {post_delta})")
        tot[(c,so,ip)] = (pre_rules,db)
    #dbs = []
    #for k,(p, db) in tot.items():
    #    print(k, p)
    #    #db.p()
    #    dbs.append(db)
    #dbs[0].diff(dbs[1])

