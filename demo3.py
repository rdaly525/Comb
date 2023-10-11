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

import hwtypes as ht
from peak import family_closure, Peak
from comb.frontend.comb_peak import CombPeak
from comb.frontend.ast import QSym
BV = ht.BitVector

def PeakPE(N: int):
    @family_closure
    def PeakPE_fc(family):
        @family.assemble(locals(), globals())
        class PE(Peak):
            def __call__(self, x: BV[N], y: BV[N], c: BV[N], instr: BV[2]) -> BV[N]:
                if instr == 3:
                    return x + y
                elif instr == 2:
                    return x - y
                elif instr == 1:
                    return x * y
                else:
                    return x + c
        return PE
    return PeakPE_fc

class CombPE(CombPeak):
    name = QSym("peak", "PE")
    def __init__(self):
        super().__init__(PeakPE, 1, lambda N: ((N,N,N,2),N), ((False, False, True, True),False))

PE = CombPE()


from time import time
from comb.frontend.stdlib import GlobalModules
gmbv = GlobalModules["bv"]

add_file = '''
Comb test.add_const
Param N: Int
In i0 : BV[N]
In i1 : CBV[N]
Out o0 : BV[N]
t = bv.abs_const[N](i1)
o0 = bv.add[N](i0, t)

Comb test.ite
Param N: Int
In sel : BV[1]
In i0 : BV[N]
In i1 : BV[N]
Out o0 : BV[N]
zeros = bv.const[N-1,0]()
not_sel = bv.not_[1](sel)
sel_ext = bv.concat[1, N-1](sel, zeros)
not_sel_ext = bv.concat[1, N-1](not_sel, zeros)
sel0 = bv.mul[N](i0, sel_ext)
sel1 = bv.mul[N](i1, not_sel_ext)
o0 = bv.or_[N](sel0, sel1)

Comb test.simplePE
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : CBV[N]
In instr : CBV[2]
Out o0 : BV[N]
t = bv.abs_const[N](i2)
bvinstr = bv.abs_const[2](instr)
bvinstr0 = bv.slice[2, 0, 1](bvinstr)
bvinstr1 = bv.slice[2, 1, 2](bvinstr)
sum = bv.add[N](i0, i1)
diff = bv.sub[N](i0, i1)
prod = bv.mul[N](i0, i1)
addc = bv.add[N](i0, t)
t0 = test.ite[N](bvinstr0, sum, diff)
t1 = test.ite[N](bvinstr0, prod, addc)
o0 = test.ite[N](bvinstr1, t0, t1)
'''

obj = compile_program(add_file)
N = 4
lhs = [
    gmbv.add[N],
    gmbv.sub[N],
    gmbv.mul[N],
    obj.get("test","add_const")[N]
]
rhs = [
    PE[N]
    # obj.get("test","simplePE")[N]
]

costs = [1]

solver_opts = SolverOpts(verbose=0, solver_name='btor', timeout=5, log=False)

max_outputs = None
C,K = 1,1
maxIR = 2
maxISA = 2
opMaxIR = None
opMaxISA = None
dce = 1
cse = 1
O_order = 1
start_time = time()
LC, E, CMP = 1, 1, 1
LC_test = 1
gen_consts = False, True

rd = RuleDiscovery(
    lhss=lhs,
    rhss=rhs,
    maxL=maxIR,
    maxR=maxISA,
    gen_consts=gen_consts,
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

