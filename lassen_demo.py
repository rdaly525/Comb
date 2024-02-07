
# import itertools
# import os
# import pytest

# from comb import Comb
from comb.frontend.compiler import compile_program
# from comb.synth.comb_encoding import CombEncoding
# from comb.synth.comm_synth import set_comm
# from comb.synth.pattern import SymOpts
# from comb.synth.rule import Rule, RuleDatabase
# from comb.synth.rule_discover import RuleDiscovery
# from comb.synth.solver_utils import SolverOpts
# from comb.synth.utils import _list_to_counts

import hwtypes as ht
# from peak import family_closure, Peak, Const

from comb.frontend.ast import QSym
from comb.frontend.comb_peak import CombPeak
from comb.frontend.ir import CombSpecialized
from comb.frontend.stdlib import CBVSynthConst
from comb.synth.comm_synth import set_comm
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts
# from hwtypes.adt import Enum, Product
import hwtypes.smt_utils as fc
from peak.family import PyFamily, SMTFamily
from lassen.alu import ALU_t, Signed_t
from lassen.cond import Cond_t
from lassen.common import DATAWIDTH, Global
from lassen.isa import Inst_fc
from lassen.lut import LUT_t_fc
from lassen.mode import gen_register_mode, gen_bit_mode, Mode_t
from lassen.sim import PE_fc
from peak import family_closure, Peak, Const
from peak.assembler import AssembledADT, Assembler
from time import time
import os
import pickle
from multiset import Multiset

solver_opts = SolverOpts(verbose=0, solver_name='bitwuzla', timeout=2000, log=False)
def parameterize_pe():
    @family_closure
    def ExpandedPE_fc(family):
        Bit = family.BitVector[1]
        Data = family.BitVector[DATAWIDTH]
        PE = PE_fc(family)
        Inst = Inst_fc(family)
        instc = family.get_constructor(Inst)
        LUT_t, _ = LUT_t_fc(family)

        @family.assemble(locals(), globals())
        class ExpandedPE(Peak):
            def __init__(self):
                self.PE = PE()

            def __call__(
                self,
                # const instruction inputs
                inst_op: ALU_t,
                inst_signed: Signed_t,
                inst_lut: LUT_t,
                inst_cond: Cond_t,
                inst_rega: Mode_t,
                inst_data0: Data,
                inst_regb: Mode_t,
                inst_data1: Data,
                inst_regc: Mode_t,
                inst_data2: Data,
                inst_regd: Mode_t,
                inst_bit0: Bit,
                inst_rege: Mode_t,
                inst_bit1: Bit,
                inst_regf: Mode_t,
                inst_bit2: Bit,
                # data inputs
                data0: Data,
                data1: Data,
                data2: Data,
                bit0: Bit,
                bit1: Bit,
                bit2: Bit,
                clk_en: Global(Bit),
            ) -> (Data, Bit):
                #inst_op = opc(alu = inst_op)

                inst_bit0 = inst_bit0[0]
                inst_bit1 = inst_bit1[0]
                inst_bit2 = inst_bit2[0]
                bit0 = bit0[0]
                bit1 = bit1[0]
                bit2 = bit2[0]
                clk_en = clk_en[0]

                inst = instc(inst_op, 
                             inst_signed,
                             inst_lut,
                             inst_cond,
                             inst_rega,
                             inst_data0,
                             inst_regb,
                             inst_data1,
                             inst_regc,
                             inst_data2,
                             inst_regd,
                             inst_bit0,
                             inst_rege,
                             inst_bit1,
                             inst_regf,
                             inst_bit2
                             )

                res, cond, _, _, _ =  self.PE(inst, data0, data1, data2, bit0, bit1, bit2, clk_en)
                return Data(res), Bit(cond)
            
        return ExpandedPE
    
    return ExpandedPE_fc


class CombPE(CombPeak):
    name = QSym("peak", "PE")
    def __init__(self):

        def type_gen():
            OPWIDTH = 5
            SIGNEDWIDTH = 1
            LUTWIDTH = 8
            CONDWIDTH = 5
            MODEWIDTH = 2
            return ( 
                (
                    #const instructions
                    OPWIDTH, 
                    SIGNEDWIDTH, 
                    LUTWIDTH,
                    CONDWIDTH,
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, 1, 
                    MODEWIDTH, 1, 
                    MODEWIDTH, 1, 
                    #data inputs
                    DATAWIDTH, DATAWIDTH, DATAWIDTH, 
                    1, 1, 1,
                    1
                ),
                (DATAWIDTH, 1)
            )

        consts = (
            (True,) * 16 + (False,) * 7,
            (False, False)
        )

        super().__init__(parameterize_pe, 0, type_gen, consts)
        set_comm(self, solver_opts)

def CombPE_constraints(in_lvars, out_lvars, in_vars, out_vars):
    cond = []
    family = SMTFamily()
    Inst = Inst_fc(family)
    instc = family.get_constructor(Inst)
    def convert_bit(b):
        assert isinstance(b, family.BitVector)
        if b.num_bits == 1:
            return b[0]
        return b

    inst_in_vars = tuple(in_vars[0:2]) +  tuple(convert_bit(b) for b in in_vars[2:16])
    inst = instc(*inst_in_vars)
    cond.append(type(inst)._is_valid_(inst._value_))
    cond.append(fc.And([inst_in_vars[i] != Mode_t.DELAY._value_ for i in [4,6,8,10,12,14]]).to_hwtypes())
    return fc.And(cond).to_hwtypes()

combPE = CombPE()[()]
combPE.constraints = CombPE_constraints

from comb.frontend.stdlib import GlobalModules
BV = GlobalModules["bv"]

lhs = [
    BV.abs_const[DATAWIDTH],
    BV.abs_const[1],

    BV.not_[DATAWIDTH],
    BV.and_[DATAWIDTH],
    BV.or_[DATAWIDTH],
    BV.xor[DATAWIDTH],
    BV.not_[1],
    BV.and_[1],
    BV.or_[1],
    BV.xor[1],

    BV.lshr[DATAWIDTH],
    BV.ashr[DATAWIDTH],
    BV.shl[DATAWIDTH],

    BV.abs[DATAWIDTH],
    BV.add[DATAWIDTH],
    BV.sub[DATAWIDTH],
    BV.mul[DATAWIDTH],
    BV.neg[DATAWIDTH],
    BV.smax[DATAWIDTH],
    BV.smin[DATAWIDTH],
    BV.umax[DATAWIDTH],
    BV.umin[DATAWIDTH],
    BV.mult_middle[DATAWIDTH],

    BV.eq[DATAWIDTH],
    BV.neq[DATAWIDTH],
    BV.slt[DATAWIDTH],
    BV.sgt[DATAWIDTH],
    BV.sle[DATAWIDTH],
    BV.sge[DATAWIDTH],
    BV.ult[DATAWIDTH],
    BV.ugt[DATAWIDTH],
    BV.ule[DATAWIDTH],
    BV.uge[DATAWIDTH],
    BV.mux[DATAWIDTH]
]
rhs = [
    combPE, 
]
costs = [1]

max_outputs = None
C,K = 1,1
maxIR = 2
maxISA = 1
opMaxIR = None
opMaxISA = None
dce = 1
cse = 1
start_time = time()
LC, E, CMP = 1, 1, 1
LC_test = 1
gen_consts = False, True
gen_dont_cares = True, True
simplify_dont_cares = True, True
simplify_gen_consts = False, True
num_proc = 8

rd = RuleDiscovery(
    lhss=lhs,
    rhss=rhs,
    maxL=maxIR,
    maxR=maxISA,
    gen_consts=gen_consts,
    gen_dont_cares=gen_dont_cares,
    simplify_dont_cares=simplify_dont_cares,
    simplify_gen_consts=simplify_gen_consts,
    opMaxL=opMaxIR,
    opMaxR=opMaxISA,
)
ir_opts = (dce, cse)
narrow_opts = (C, K)
E_opts = (LC, E, CMP)
bin_search = [True, False]

#load excluded pats or generate them
ir_exclude_filename = f"lassen/exclude_{maxIR}.pkl"
if os.path.exists(ir_exclude_filename):
    print(f"Found excluded pats file {ir_exclude_filename}")
    with open(ir_exclude_filename, 'rb') as f:
        exclude_pats = pickle.load(f)
else:
    print("Generating excluded pats")
    exclude_pats = rd.gen_ir_optimizations(E_opts, ir_opts, narrow_opts, solver_opts, bin_search[0])

excluded_pats = []
for i,pat in enumerate(exclude_pats):
    print("excluded", i, flush=True)
    print(pat.to_comb())
    print("*"*80)
    excluded_pats.append(pat)
if not os.path.exists(ir_exclude_filename):
    print(f"Saving excluded pats to {ir_exclude_filename}")
    for pat in excluded_pats:
        for op in pat.ops:
            if hasattr(op, "prev_eval"):
                op.eval = op.prev_eval
                delattr(op, "prev_eval")
    with open(ir_exclude_filename, 'wb') as f:
        pickle.dump(excluded_pats, f)

if LC_test:
    ga = rd.gen_lowcost_rules_mp(E_opts, ir_opts, narrow_opts, costs, max_outputs, solver_opts, bin_search, excluded_pats, num_proc)
else:
    ga = rd.gen_all_rules(E_opts, ir_opts, narrow_opts, max_outputs, solver_opts, bin_search, excluded_pats)
for ri, rule in enumerate(ga):
    print("RULE", ri, time()-start_time)
    print(rule)
    print("*"*80, flush = True)
db = rd.rdb

rule_database_filename = f"lassen/rules_{maxIR}_{maxISA}.pkl"
if not os.path.exists(rule_database_filename):
    print(f"Saving rules to {rule_database_filename}")
    all_rules = []
    for k,rules in db.rules.items():
        t = db.time[k]
        for rule in rules:
            for op in rule.lhs.ops:
                if hasattr(op, "prev_eval"):
                    op.eval = op.prev_eval
                    delattr(op, "prev_eval")
            for i,op in enumerate(rule.rhs.ops):
                if hasattr(op, "prev_eval"):
                    op.eval = op.prev_eval
                    delattr(op, "prev_eval")
                elif isinstance(op, CombSpecialized) and isinstance(op.comb, CombPeak):
                    rule.rhs.ops[i] = 0
        all_rules.append((k, rules, t))

    with open(rule_database_filename, 'wb') as f:
        pickle.dump(all_rules, f)

for k, info in db.time_info.items():
    num_unique = info["u"]
    extra = info['e']
    sat_time = info['st']
    extra_time = info['et']
    assert extra >=0
    print(f"KIND:{k}, UNIQUE:{num_unique}, DUP: {extra}, ST: {sat_time}, ET: {extra_time}")
delta = time()-start_time
print("TOTTIME:", delta)

from comb.synth.verify import verify
prog = """\
Comb coreir.umin
Param N: Int
In a : BV[N]
In b : BV[N]
Out o : BV[N]
cmp = bv.ult[N](a,b)
o = bv.mux[N](b,a,cmp)

Comb coreir.umax
Param N: Int
In a : BV[N]
In b : BV[N]
Out o : BV[N]
cmp = bv.ugt[N](a,b)
o = bv.mux[N](b,a,cmp)

Comb coreir.smin
Param N: Int
In a : BV[N]
In b : BV[N]
Out o : BV[N]
cmp = bv.slt[N](a,b)
o = bv.mux[N](b,a,cmp)

Comb coreir.smax
Param N: Int
In a : BV[N]
In b : BV[N]
Out o : BV[N]
cmp = bv.sgt[N](a,b)
o = bv.mux[N](b,a,cmp)

Comb coreir.abs
Param N: Int
In a : BV[N]
Out o : BV[N]
t = bv.neg[N](a)
o = coreir.smax[N](a,t)

Comb coreir.mac
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](a,b)
o = bv.add[N](t,c)

Comb coreir.muladd_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](a,b)
o = bv.add[N](t,c)

Comb coreir.muladd_s1
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](b,c)
o = bv.add[N](t,a)

Comb coreir.mulsub_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](a,b)
o = bv.sub[N](t,c)

Comb coreir.scrop
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.smin[N](a,b)
o = bv.smax[N](t,c)

Comb coreir.ucrop
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.umin[N](a,b)
o = bv.umax[N](t,c)

Comb coreir.smulshr_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](a,b)
o = bv.ashr[N](t,c)

Comb coreir.staa_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](a,b)
o = bv.add[N](t,c)

Comb coreir.staa_s1
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](b,c)
o = bv.add[N](t,a)

Comb coreir.stas_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](a,b)
o = bv.sub[N](t,c)

Comb coreir.stsa_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.sub[N](a,b)
o = bv.add[N](t,c)

Comb coreir.stss_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.sub[N](a,b)
o = bv.sub[N](t,c)

Comb coreir.tadd
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](a,b)
o = bv.add[N](t,c)

Comb coreir.umulshr_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.mul[N](a,b)
o = bv.lshr[N](t,c)

Comb coreir.utaa_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](a,b)
o = bv.add[N](t,c)

Comb coreir.utaa_s1
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](b,c)
o = bv.add[N](t,a)

Comb coreir.utas_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.add[N](a,b)
o = bv.sub[N](t,c)

Comb coreir.utsa_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.sub[N](a,b)
o = bv.add[N](t,c)

Comb coreir.utss_s0
Param N: Int
In a : BV[N]
In b : BV[N]
In c : BV[N]
Out o : BV[N]
t = bv.sub[N](a,b)
o = bv.sub[N](t,c)
"""

obj = compile_program(prog, add_comm = False)
old_rules = [
        obj.get("coreir", "abs")[DATAWIDTH],
        BV.add[DATAWIDTH],
        BV.and_[DATAWIDTH],
        BV.ashr[DATAWIDTH],
        BV.and_[1],
        BV.abs_const[1],
        BV.not_[1],
        BV.or_[1],
        BV.xor[1],
        BV.abs_const[DATAWIDTH],
        BV.eq[DATAWIDTH],
        BV.lshr[DATAWIDTH],
        obj.get("coreir", "mac")[DATAWIDTH],
        BV.mul[DATAWIDTH],
        obj.get("coreir", "muladd_s0")[DATAWIDTH],
        obj.get("coreir", "muladd_s1")[DATAWIDTH],
        obj.get("coreir", "mulsub_s0")[DATAWIDTH],
        BV.mult_middle[DATAWIDTH],
        BV.mux[DATAWIDTH],
        BV.neq[DATAWIDTH],
        BV.or_[DATAWIDTH],
        obj.get("coreir", "scrop")[DATAWIDTH],
        BV.sge[DATAWIDTH],
        BV.sgt[DATAWIDTH],
        BV.shl[DATAWIDTH],
        BV.sle[DATAWIDTH],
        BV.slt[DATAWIDTH],
        obj.get("coreir", "smin")[DATAWIDTH],
        obj.get("coreir", "smax")[DATAWIDTH],
        obj.get("coreir", "smulshr_s0")[DATAWIDTH],
        obj.get("coreir", "staa_s0")[DATAWIDTH],
        obj.get("coreir", "staa_s1")[DATAWIDTH],
        obj.get("coreir", "stas_s0")[DATAWIDTH],
        obj.get("coreir", "stsa_s0")[DATAWIDTH],
        obj.get("coreir", "stss_s0")[DATAWIDTH],
        BV.sub[DATAWIDTH],
        obj.get("coreir", "tadd")[DATAWIDTH],
        obj.get("coreir", "scrop")[DATAWIDTH],
        BV.uge[DATAWIDTH],
        BV.ugt[DATAWIDTH],
        BV.ule[DATAWIDTH],
        BV.ult[DATAWIDTH],
        obj.get("coreir", "umin")[DATAWIDTH],
        obj.get("coreir", "umax")[DATAWIDTH],
        obj.get("coreir", "umulshr_s0")[DATAWIDTH],
        obj.get("coreir", "utaa_s0")[DATAWIDTH],
        obj.get("coreir", "utaa_s1")[DATAWIDTH],
        obj.get("coreir", "utas_s0")[DATAWIDTH],
        obj.get("coreir", "utsa_s0")[DATAWIDTH],
        obj.get("coreir", "utss_s0")[DATAWIDTH],
        ]
old_rule_matched = [False for _ in old_rules]
new_rule_matched = [False for _ in range(db.num_rules)]
rulei = 0
for k,rules in db.rules.items():
    for rule in rules:
        rule = rule.lhs.to_comb()
        for i,old_rule in enumerate(old_rules):
            if Multiset(rule.get_type()[0]) == Multiset(old_rule.get_type()[0]) and Multiset(rule.get_type()[1]) == Multiset(old_rule.get_type()[1]):
                if verify(old_rule, rule, enum_io_order = True) is None:
                    old_rule_matched[i] = True
                    new_rule_matched[rulei] = True
                    #print("Match")
                    #print(old_rule)
                    #print(rule)
                    #print("*"*10)
        if not new_rule_matched[rulei]:
            print(rule)
        rulei += 1
print(old_rule_matched)
print(new_rule_matched)
print("Total existing matched", sum(old_rule_matched))
print("Total existing unique", sum(not x for x in old_rule_matched))
print("Total synthesized matched", sum(new_rule_matched))
print("Total synthesized unique", sum(not x for x in new_rule_matched))




c = db.find_all_composites()
print(c)
assert c == []

