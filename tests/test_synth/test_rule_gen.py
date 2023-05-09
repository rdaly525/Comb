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
from comb.synth.utils import _list_to_counts

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/simple.comb"
import typing as tp


from timeit import default_timer as time

@pytest.mark.parametrize("pat_en_t", [
    CombEncoding,
])
def test_isa(pat_en_t):
    N = 8
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    ir = [c[N] for c in obj.get_from_ns("ir")]
    isa = [c[N] for c in obj.get_from_ns("isa")]
    print([c.name for c in isa])
    #costs = [11, 8, 30, 18, 5,5,5,5]
    costs = [11, 8, 30, 18]
    num_isa = 4
    isa = isa[:num_isa]

    costs = costs[:num_isa]
    if True:
        ir = ir*4
        isa = isa*4
        costs = costs*4
    for op in [*ir, *isa]:
        set_comm(op)
    for i in (1,3):
        assert ir[i].comm_info == ([0,1],)
    assert isa[0].comm_info == ([0,1],)
    assert isa[3].comm_info == ([0,1,2],)

    def custom_filter(lhs_ids, rhs_ids):
        return False
        #if sorted(lhs_ids) != sorted([1,1,4]):
        #    return True
        #if 2 in rhs_ids and 3 in rhs_ids:
        #    return True


    #maxIR = 3
    #maxISA = 3
    #const_synth = True
    const_synth = False
    opMaxIR = {0:1, 1:2, 2:2, 3:1}
    opMaxIR = None
    opMaxISA = {0:1, 1:2, 2:2, 3:2}
    opMaxISA = None
    #for c, so, ip in itertools.product((1, 0), repeat=3):
    only_lhs_sym = False
    res_dir = f"{dir}/../../results/small"
    for (E, to, maxIR, maxISA) in (
        (1, 10, 1, 1),
        (0, 10, 1, 1),
    ):
        opts = SolverOpts(verbose=0, solver_name='z3', timeout=to, log=True)
        for c, so, ip in (
            (0,0,0),
            #(1,0,0),
            #(1,1,1),
            #(0,0,0),
            #(0,0,1),
            #(0,1,0),
            #(1,1,0),
            #(1,0,1),
        ):
            pfile = f"{res_dir}/res{maxIR}_{maxISA}_{E}{c}{so}{ip}_{to}.pickle"
            rfile = f"{res_dir}/res{maxIR}_{maxISA}_{E}{c}{so}{ip}_{to}.comb"
            print(f"\nEXCLUDE: {E}")
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
                pgf=E,
                igf=E,
                const_synth=const_synth,
                only_lhs_sym=only_lhs_sym,
            )
            print(f"N", rd.num_queries())
            for ri, rule in enumerate(rd.gen_all(opts)):
                #print("RULE", ri)
                #print(rule)
                #print("*"*80)
                pass
            rd.rdb.pickle_info(pfile)
            rd.rdb.save("rule", rfile)
            gen_time = time()
            #db = rd.rdb
            pre_rules = len(rd.rdb)
            ##db.post_filter()
            ##post_time = time()
            gen_delta = round(gen_time - start_time, 4)
            ##post_delta = round(post_time - gen_time, 4)
            print(f"PRE: ({pre_rules}, {gen_delta})")
            continue
            ##print(f"POST: ({len(db)}, {post_delta})")
            #table = db.sort(maxIR, maxISA)
            #for l in range(1,maxIR+1):
            #    for r in range(1,maxISA+1):
            #        print(f"[{l}][{r}] = {table[l][r]}")

            #for ri, rule in enumerate(db.rules):
            #    print("*"*80)
            #    print(rule)
         #dbs = []
        #for k,(p, db) in tot.items():
        #    print(k, p)
        #    #db.p()
        #    dbs.append(db)
        #dbs[0].diff(dbs[1])

