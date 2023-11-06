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

from time import time

prog = """\
Comb ir.add
In a : BV[2]
In b : BV[2]
Out o : BV[2]
o = bv.add[2](a,b)

Comb ir.ext_add
In a : BV[2]
In b : BV[2]
In ci : BV[1]
Out o : BV[3]
zero_1 = bv.const[1,0]()
zero_2 = bv.const[2,0]()
a_ext = bv.concat[2,1](a, zero_1)
b_ext = bv.concat[2,1](b, zero_1)
ci_ext = bv.concat[1,2](ci, zero_2)
t = bv.add[3](a_ext,b_ext)
o = bv.add[3](t,ci_ext)

Comb isa.fa
In ci : BV[1] 
In a : BV[1]
In b : BV[1]
Out co : BV[1]
Out s : BV[1]
a_xor_b = bv.xor[1](a, b)
s = bv.xor[1](a_xor_b, ci)
a_and_b = bv.and_[1](a, b)
t = bv.and_[1](ci, a_xor_b)
co = bv.or_[1](t, a_and_b)

Comb isa.ha
In a : BV[1]
In b : BV[1]
Out co : BV[1]
Out s : BV[1]
s = bv.xor[1](a, b)
co = bv.and_[1](a, b)

Comb isa.concat2
In a : BV[1]
In b : BV[1]
Out o : BV[2]
o = bv.concat[1,1](a,b)

Comb isa.concat3
In a : BV[1]
In b : BV[1]
In c : BV[1]
Out o : BV[3]
t = isa.concat2(a,b)
o = bv.concat[2,1](t,c)

Comb isa.split
In a : BV[2]
Out o0 : BV[1]
Out o1 : BV[1]
o0 = bv.slice[2,0,1](a)
o1 = bv.slice[2,1,2](a)
"""

import typing as tp

obj = compile_program(prog)
ir = [c for c in obj.get_from_ns("ir")]
isa = [c for c in obj.get_from_ns("isa")]
print([c.name for c in isa])
costs = [3,2,1,1,1]

solver_opts = SolverOpts(verbose=0, solver_name='btor', timeout=5, log=False)

def test_genall(LC_test, LC, E, CMP, C, K):
    if not LC_test:
        assert not LC
    print("F:", LC_test, LC, E, CMP, C, K)
    max_outputs = None
    maxIR = 2
    maxISA = 6
    opMaxIR = None
    opMaxISA = None
    dce = 1
    cse = 1
    O_order = 1
    start_time = time()
    rd = RuleDiscovery(
        lhss=ir,
        rhss=isa,
        maxL=maxIR,
        maxR=maxISA,
        opMaxL=opMaxIR,
        opMaxR=opMaxISA,
    )
    ir_opts = (dce, cse)
    narrow_opts = (C, K, O_order)
    E_opts = (LC, E, CMP)
    if LC_test:
        ga = rd.gen_lowcost_rules(E_opts, ir_opts, narrow_opts, costs, max_outputs, solver_opts)
    else:
        ga = rd.gen_all_rules(E_opts, ir_opts, narrow_opts, max_outputs, solver_opts)
    for ri, rule in enumerate(ga):
        print("RULE", ri, flush=True)
        print(rule)
        print("*"*80)
    db = rd.rdb
    for k, info in db.time_info.items():
        num_unique = info["u"]
        extra = info['e']
        sat_time = info['st']
        extra_time = info['et']
        assert extra >=0
        print(f"KIND:{k}, UNIQUE:{num_unique}, DUP: {extra}, ST: {sat_time}, ET: {extra_time}")
    delta = time()-start_time
    print("TOTTIME:", delta)

test_genall(1,1,1,1,1,1)


