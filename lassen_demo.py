
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

solver_opts = SolverOpts(verbose=0, solver_name='bitwuzla', timeout=300, log=False)
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

add_file = '''
Comb test.add_const
Param N: Int
In i0 : BV[N]
In i1 : CBV[N]
Out o0 : BV[N]
t = bv.abs_const[N](i1)
o0 = bv.add[N](i0, t)
'''
obj = compile_program(add_file)

from comb.frontend.stdlib import GlobalModules
BV = GlobalModules["bv"]

lhs = [
    BV.not_[DATAWIDTH],
    BV.and_[DATAWIDTH],
    BV.or_[DATAWIDTH],
    BV.xor[DATAWIDTH],
    BV.lshr[DATAWIDTH],
    BV.ashr[DATAWIDTH],
    BV.shl[DATAWIDTH],

    BV.add[DATAWIDTH],
    BV.sub[DATAWIDTH],
    BV.mul[DATAWIDTH],

    BV.eq[DATAWIDTH],
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
maxIR = 1
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
exclude_pats = rd.gen_ir_optimizations(E_opts, ir_opts, narrow_opts, solver_opts, bin_search[0])
excluded_pats = []
for i,pat in enumerate(exclude_pats):
    print("excluded", i, flush=True)
    print(pat.to_comb())
    print("*"*80)
    excluded_pats.append(pat)
if LC_test:
    ga = rd.gen_lowcost_rules_mp(E_opts, ir_opts, narrow_opts, costs, max_outputs, solver_opts, bin_search, excluded_pats, num_proc)
else:
    ga = rd.gen_all_rules(E_opts, ir_opts, narrow_opts, max_outputs, solver_opts, bin_search, excluded_pats)
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
c = db.find_all_composites()
print(c)
assert c == []

