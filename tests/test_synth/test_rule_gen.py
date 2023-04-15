import itertools
import os

import pytest

from comb import Comb
from comb.frontend.compiler import compile_program
from comb.synth.comb_encoding import CombEncoding
from comb.synth.comm_synth import set_comm
from comb.synth.pattern import SymOpts
from comb.synth.rule import Rule, RuleDatabase
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/simple.comb"
import typing as tp


from timeit import default_timer as time

@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
])
def test_isa(pat_en_t):
    N = 16
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    ir = [c[N] for c in obj.get_from_ns("ir")]
    isa = [c[N] for c in obj.get_from_ns("isa")]
    print([c.name for c in isa])
    #costs = [11, 8, 30, 18, 5,5,5,5]
    costs = [11, 8, 30, 18, 0,0,0,0]
    num_isa = 8
    isa = isa[:num_isa]
    costs = costs[:num_isa]
    for op in [*ir, *isa]:
        set_comm(op)
    for i in (1,3):
        assert ir[i].comm_info
    assert isa[0].comm_info

    def custom_filter(lhs_ids, rhs_ids):
        if any((i in rhs_ids) and len(rhs_ids)>1 for i in range(4,8)):
            return True
        if rhs_ids == [0,0,2]:
            return True
        if 2 in rhs_ids and 3 in rhs_ids:
            return True

    opts = SolverOpts(verbose=1, max_iters=0, solver_name='z3', timeout=120, log=True)
    maxIR = 3
    maxISA = 2
    opMaxIR = {0:1, 1:2, 2:1, 3:1, 4:3}
    #opMaxIR = {0:0, 1:0, 2:1, 3:0}
    opMaxISA = {0:1, 1:1, 2:1, 3:1, **{4+i:1 for i in range(4)}}
    #for c, so, ip in itertools.product((1, 0), repeat=3):
    for c, so, ip in (
        (1,1,1),
    ):
        print(f"\nSYM: ({c},{so},{ip})")
        sym_opts = SymOpts(comm=c, same_op=so, input_perm=ip)

        start_time = time()
        rd = RuleDiscovery(
            lhss=ir,
            rhss=isa,
            costs=costs,
            maxL=maxIR,
            maxR=maxISA,
            pat_en_t=pat_en_t,
            sym_opts=sym_opts,
            opMaxL=opMaxIR,
            opMaxR=opMaxISA,
            custom_filter=custom_filter,
            pgf=True,
            igf=True
        )
        for ri, rule in enumerate(rd.gen_all(opts)):
            print("RULE", ri)
            print(rule)
            print("*"*80)
            pass
        gen_time = time()
        db = rd.rdb
        pre_rules = len(db)
        db.post_filter()
        post_time = time()
        gen_delta = round(gen_time - start_time, 4)
        post_delta = round(post_time - gen_time, 4)
        print(f"PRE: ({pre_rules}, {gen_delta})")
        print(f"POST: ({len(db)}, {post_delta})")
        table = db.sort(maxIR, maxISA)
        for l in range(1,maxIR+1):
            for r in range(1,maxISA+1):
                print(f"[{l}][{r}] = {table[l][r]}")

        for ri, rule in enumerate(db.rules):
            print("*"*80)
            print(rule)
     #dbs = []
    #for k,(p, db) in tot.items():
    #    print(k, p)
    #    #db.p()
    #    dbs.append(db)
    #dbs[0].diff(dbs[1])

