
import hwtypes as ht
from comb.frontend.ast import QSym
from comb.frontend.comb_peak import CombPeak
from comb.frontend.ir import CombSpecialized
from comb.frontend.stdlib import CBVSynthConst
from comb.frontend.lassen.lassen_16bit import combPE
from comb.synth.comm_synth import set_comm
from comb.synth.rule import RuleDatabase
from comb.synth.utils import nT
from comb.synth.solver_utils import SolverOpts
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

from_file = f"lassen/rules_3_1_4bit.pkl"
to_file = f"lassen/rules_3_1.pkl"
from_bits = 4
to_bits = 16

rdb = RuleDatabase()
with open(from_file, 'rb') as f:
    all_rules = pickle.load(f)
    for k,rules,time in all_rules:
        print(len(rules))
        #all rules of the same k will have a handle to the same op list,
        #need to make them different lists
        for rule in rules:
            rule.lhs.ops = list(rule.lhs.ops)
            rule.rhs.ops = list(rule.rhs.ops)

        new_rules = []
        for rule in rules:
            #change op bitwidths
            synth_vals = list(rule.lhs.synth_vals)
            for i,op in enumerate(rule.lhs.ops):
                if isinstance(op, CombSpecialized) and op.pargs[0].value == from_bits:
                    assert len(op.pargs) == 1
                    new_op = op.comb[to_bits]
                    rule.lhs.ops[i] = new_op
                    if isinstance(op.comb, CBVSynthConst):
                        convert_from = [0, 1, 2**from_bits-1, 2**(from_bits-1)]
                        convert_to = [0, 1, 2**to_bits-1, 2**(to_bits-1)]
                        assert rule.lhs.synth_map[i] in convert_from
                        idx = sorted(rule.lhs.synth_map.keys()).index(i)
                        new_val = convert_to[convert_from.index(rule.lhs.synth_map[i])]
                        rule.lhs.synth_map[i] = new_val
                        synth_vals[idx] = new_val
            rule.lhs.synth_vals = tuple(synth_vals)

            synth_vals = list(rule.rhs.synth_vals)
            for i,op in enumerate(rule.rhs.ops):
                if isinstance(op, int):
                    rule.rhs.ops[i] = combPE
                elif isinstance(op, CombSpecialized) and op.pargs[0].value == from_bits:
                    assert len(op.pargs) == 1
                    new_op = op.comb[to_bits]
                    rule.rhs.ops[i] = new_op
                    if isinstance(op.comb, CBVSynthConst):
                        convert_from = [0, 1, 2**from_bits-1, 2**(from_bits-1)]
                        convert_to = [0, 1, 2**to_bits-1, 2**(to_bits-1)]
                        assert rule.rhs.synth_map[i] in convert_from
                        idx = sorted(rule.rhs.synth_map.keys()).index(i)
                        new_val = convert_to[convert_from.index(rule.rhs.synth_map[i])]
                        rule.rhs.synth_map[i] = new_val
                        synth_vals[idx] = new_val
            rule.rhs.synth_vals = tuple(synth_vals)

            rule.lhs.iT = tuple(iT if iT.n != from_bits else nT(to_bits,iT.const) for iT in rule.lhs.iT)
            rule.lhs.oT = tuple(oT if oT.n != from_bits else nT(to_bits,oT.const) for oT in rule.lhs.oT)
            rule.rhs.iT = tuple(iT if iT.n != from_bits else nT(to_bits,iT.const) for iT in rule.rhs.iT)
            rule.rhs.oT = tuple(oT if oT.n != from_bits else nT(to_bits,oT.const) for oT in rule.rhs.oT)
            rule.iT = rule.lhs.iT
            rule.oT = rule.lhs.oT

            print("verify")
            print(rule, flush = True)
            if rule.verify():
                new_rules.append(rule)
            else:
                print("Failed rule conversion:")
                print(rule)
                print("")

        rdb.add_rules(k,new_rules,time)

all_rules = []
for k,rules in rdb.rules.items():
    t = rdb.time[k]
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

with open(to_file, 'wb') as f:
    pickle.dump(all_rules, f)
