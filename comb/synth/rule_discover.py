import functools
import timeit

from comb import Comb
from comb.frontend.ast import TypeCall, BVType, IntValue
from ..frontend.stdlib import GlobalModules, CBVDontCare, BVDontCare
from comb.synth.comb_encoding import CombEncoding
from comb.synth.const_synth import ConstDiscover
from comb.synth.pattern import SymOpts, enum_dags, composite_pat, Pattern
from comb.synth.pattern_encoding import PatternEncoding
from comb.synth.rule import Rule, RuleDatabase
from comb.synth.rule_synth import RuleSynth
from comb.synth.solver_utils import SolverOpts, smt_solve_all, get_var
from comb.synth.utils import _list_to_counts, flat, _to_int, types_to_nTs, _list_to_dict, ge0_cnts, sub_cnts, _m_subseteq
import hwtypes.smt_utils as fc
import hwtypes as ht
import typing as tp
import itertools as it
from dataclasses import dataclass
#This is the motherload of classes
#It is the discovery engine that leverages the symbolic instruction selection
from more_itertools import distinct_combinations as multicomb


def _smart_iter(mL: int, mR: int):
    for s in range(2, mL+mR+1):
        for l in range(1, s):
            r = s-l
            if l <= mL and r <= mR:
                yield (l, r)

def smart_iter(mL: int, mR: int):
    for r in range(1,mR+1):
        for l in range(1,mL+1):
            yield (l, r)

def print_iot(iT, oT):
    T_strs = ["(" + ", ".join(str(T) for T in Ts) + ")" for Ts in (iT, oT)]
    print(f"IOT: {T_strs[0]} -> {T_strs[1]}")


def print_kind(l_ids, r_ids):
    id_strs = ["(" + ", ".join(str(id) for id in ids) + ")" for ids in (l_ids, r_ids)]
    print(f"KIND: {id_strs[0]} -> {id_strs[1]}")

def get_cnt(op, k):
    return {T:len(ids) for T, ids in types_to_nTs(op.get_type()[k]).items()}

def count(l):
    ret = {}
    for d in l:
        for n, v in d.items():
            ret[n] = ret.get(n, 0) + v
    return ret

def T_count(ops):
    iTs = count([get_cnt(op, 0) for op in ops])
    oTs = count([get_cnt(op, 1) for op in ops])
    return iTs, oTs

@dataclass
class RuleDiscovery:
    lhss: tp.List[Comb]
    rhss: tp.List[Comb]
    maxL: int
    maxR: int
    gen_consts: tp.Tuple[bool, bool]
    gen_dont_cares: tp.Tuple[bool, bool]
    simplify_gen_consts: tp.Tuple[bool, bool]
    simplify_dont_cares: tp.Tuple[bool, bool]
    opMaxL: tp.Mapping[int, int] = None
    opMaxR: tp.Mapping[int, int] = None
    pat_en_t: tp.Type[PatternEncoding] = CombEncoding

    def __post_init__(self):
        if self.opMaxL is None:
            self.opMaxL = {i:self.maxL for i in range(len(self.lhss))}
        if self.opMaxR is None:
            self.opMaxR = {i:self.maxR for i in range(len(self.rhss))}
        self.lhss = list(self.lhss)
        self.rhss = list(self.rhss)
        self.rdb: RuleDatabase = RuleDatabase()
        self.lhs_name_to_id = {comb.qualified_name:i for i, comb in enumerate(self.lhss)}
        self.rhs_name_to_id = {comb.qualified_name:i for i, comb in enumerate(self.rhss)}
        if self.simplify_dont_cares[0]:
            assert self.gen_dont_cares[0]
        if self.simplify_dont_cares[1]:
            assert self.gen_dont_cares[1]
        if self.simplify_gen_consts[0]:
            assert self.gen_consts[0]
        if self.simplify_gen_consts[1]:
            assert self.gen_consts[1]

    def allT(self, lhs_ops, rhs_ops, l_dont_care_T, r_dont_care_T, max_outputs):
        # generate all possible program input and output type combinations

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)

        if not self.simplify_dont_cares[0]:
            for T in l_dont_care_T:
                assert lop_iTs[T] > 0
                lop_iTs[T] -= 1

        if not self.simplify_dont_cares[1]:
            for T in r_dont_care_T:
                assert rop_iTs[T] > 0
                rop_iTs[T] -= 1

        max_iTs = {T:min(lop_iTs[T], rop_iTs[T]) for T in set(lop_iTs.keys()) & set(rop_iTs.keys())}
        max_oTs = {T:min(lop_oTs[T], rop_oTs[T]) for T in set(lop_oTs.keys()) & set(rop_oTs.keys())}

        max_inputs = sum(max_iTs.values())
        if max_outputs is None:
            max_outputs = sum(max_oTs.values())
        else:
            max_outputs = min(max_outputs, sum(max_oTs.values()))

        iTs_all = flat((T,)*c for T,c in max_iTs.items())
        oTs_all = flat((T,)*c for T,c in max_oTs.items())

        for num_out in range(max_outputs, 0, -1):
            for oTs_sel in multicomb(oTs_all, num_out):
                for num_in in range(max_inputs, -1, -1):
                    for iTs_sel in multicomb(iTs_all, num_in):
                        yield (tuple(iTs_sel), tuple(oTs_sel))

    def all_synth_T(self, iT, oT, lhs_ops, rhs_ops, l_dont_care_T, r_dont_care_T):
        # generate all possible combinations of constants that can be synthesized

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)
        
        lop_const_iTs = {k:v for k,v in lop_iTs.items() if k.const}
        rop_const_iTs = {k:v for k,v in rop_iTs.items() if k.const}

        # inputs must go somewhere, remove their counts from the 
        # possible number of constants that can be generate
        for T in iT:
            if not T.const:
                continue
            if not self.simplify_gen_consts[0]:
                assert lop_const_iTs[T] > 0
                lop_const_iTs[T] -= 1
            if not self.simplify_gen_consts[1]:
                assert rop_const_iTs[T] > 0
                rop_const_iTs[T] -= 1

        if not self.simplify_dont_cares[0]:
            for T in l_dont_care_T:
                if not T.const:
                    continue
                assert lop_const_iTs[T] > 0
                lop_const_iTs[T] -= 1

        if not self.simplify_dont_cares[1]:
            for T in r_dont_care_T:
                if not T.const:
                    continue
                assert rop_const_iTs[T] > 0
                rop_const_iTs[T] -= 1

        l_gen_consts, r_gen_consts = self.gen_consts

        l_synth_all = []
        if l_gen_consts:
            l_synth_all = flat((T,)*c for T,c in lop_const_iTs.items())

        r_synth_all = []
        if r_gen_consts:
            r_synth_all = flat((T,)*c for T,c in rop_const_iTs.items())

        if self.simplify_gen_consts[0]: 
            l_synth_sels = [l_synth_all]
        else:
            l_synth_sels = [l_synth_sel for num_l in range(len(l_synth_all) + 1) 
                                        for l_synth_sel in multicomb(l_synth_all, num_l)]
        if self.simplify_gen_consts[1]: 
            r_synth_sels = [r_synth_all]
        else:
            r_synth_sels = [r_synth_sel for num_r in range(len(r_synth_all) + 1) 
                                        for r_synth_sel in multicomb(r_synth_all, num_r)]
        
        return it.product(l_synth_sels, r_synth_sels)


    def all_dont_care_T(self, lhs_ops, rhs_ops):
        # generate all possible combinations of dont cares that can be synthesized

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)

        l_gen_dont_cares, r_gen_dont_cares = self.gen_dont_cares

        if self.simplify_dont_cares[0]:
            lop_iTs = {T:1 for T in lop_iTs.keys()}
        if self.simplify_dont_cares[1]:
            rop_iTs = {T:1 for T in rop_iTs.keys()}

        l_dont_care_all = []
        if l_gen_dont_cares:
            l_dont_care_all = flat((T,)*c for T,c in lop_iTs.items())

        r_dont_care_all = []
        if r_gen_dont_cares:
            r_dont_care_all = flat((T,)*c for T,c in rop_iTs.items())
        
        if self.simplify_dont_cares[0]: 
            l_dont_care_sels = [l_dont_care_all]
        else:
            l_dont_care_sels = [l_dont_care_sel for num_l in range(len(l_dont_care_all), -1, -1) 
                                        for l_dont_care_sel in multicomb(l_dont_care_all, num_l)]
        if self.simplify_dont_cares[1]: 
            r_dont_care_sels = [r_dont_care_all]
        else:
            r_dont_care_sels = [r_dont_care_sel for num_r in range(len(r_dont_care_all), -1, -1) 
                                        for r_dont_care_sel in multicomb(r_dont_care_all, num_r)]
        
        return it.product(l_dont_care_sels, r_dont_care_sels)


    def valid_program_components(self, iT, oT, lhs_ops, rhs_ops, l_synth_T, r_synth_T, l_dont_care_T, r_dont_care_T):
        # return True if the program components could possibly form a valid program
        # else return False

        # TODO: could make this a more elaborate check in the future if too many
        # hopeless programs make it past this check and slow down the synthesis

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)

        lsrcs_no_i = set(lop_oTs.keys()) | set(l_synth_T) | set(l_dont_care_T)
        rsrcs_no_i = set(rop_oTs.keys()) | set(r_synth_T) | set(r_dont_care_T)
        lsncs_no_o = set(lop_iTs.keys())
        rsncs_no_o = set(rop_iTs.keys())

        #all non-output sncs must have a src
        if not lsncs_no_o <= (set(iT) | lsrcs_no_i) or not rsncs_no_o <= (set(iT) | rsrcs_no_i):
            return False

        #all outputs must have a non-input src
        if not set(oT) <= lsrcs_no_i or not set(oT) <= rsrcs_no_i:
            return False

        return True

    #Finds all composite rules


    # Finds all combinations of rules that exactly match the lhs and rhs
    def all_composite_msets(self, lhs_ids, rhs_ids, iT, oT, lhs_synth_ops, rhs_synth_ops, opts:SolverOpts):
        NI = len(iT)
        NO = len(oT)
        lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])
        rhs_op_cnt = _list_to_counts([self.rhss[rid].qualified_name for rid in rhs_ids])

        for op in lhs_synth_ops:
            lhs_op_cnt[op.qualified_name] = lhs_op_cnt.get(op.qualified_name, 0) + 1
        for op in rhs_synth_ops:
            rhs_op_cnt[op.qualified_name] = rhs_op_cnt.get(op.qualified_name, 0) + 1

        #Prefiltering
        poss_rules = {}
        #ri_N = {}
        ri_to_k = {}
        for ri, (k, i, rule) in enumerate(self.rdb.enum_rules()):
            ri_to_k[ri] = (k, i)
            l_eq = rule.lhs.op_cnt == lhs_op_cnt
            r_eq = rule.rhs.op_cnt == rhs_op_cnt
            if l_eq and r_eq and rule.NI >= NI and rule.NO >= NO:
                if opts.log:
                    print("RCNT", {ri:1},flush=True)
                yield [(rule, 1)]
                continue
            l_subseteq = _m_subseteq(rule.lhs.op_cnt_no_dont_cares, lhs_op_cnt)
            r_subseteq = _m_subseteq(rule.rhs.op_cnt_no_dont_cares, rhs_op_cnt)
            if l_subseteq and r_subseteq:
                poss_rules[ri] = rule
                #ri_N[ri] = (I_max(rule.lhs.ops), I_max(rule.rhs.ops))
        if len(poss_rules) == 0:
            return

        #Early out if there is not at least one matching op over all poss rules
        #poss_ops = functools.reduce(lambda s0, s1: s0|s1, [set(op_cnt.keys()) for op_cnt,_,_ in poss_rules.values()])
        #if poss_ops != set(lhs_op_cnt.keys()):
        #    return

        rvarT = ht.SMTBitVector[32]
        max_rvar = max(cnt for cnt in it.chain(lhs_op_cnt.values(), rhs_op_cnt.values()))
        lhs_op_cnts = {op:rvarT(0) for op in lhs_op_cnt.keys()}
        rhs_op_cnts = {op:rvarT(0) for op in rhs_op_cnt.keys()}
        rvars = {ri:get_var(f"R{ri}", 32) for ri in poss_rules.keys()}
        for ri, rule in poss_rules.items():
            rvar = rvars[ri]

            #ir cnt
            for op, cnt in rule.lhs.op_cnt_no_dont_cares.items():
                assert op in lhs_op_cnts
                lhs_op_cnts[op] += rvar*cnt
            #isa cnt
            for op, cnt in rule.rhs.op_cnt_no_dont_cares.items():
                assert op in rhs_op_cnts
                rhs_op_cnts[op] += rvar*cnt

        lconds = []
        for op, cnt in lhs_op_cnts.items():
            lconds.append(cnt <= lhs_op_cnt[op])
        rconds = []
        for op, cnt in rhs_op_cnts.items():
            rconds.append(cnt <= rhs_op_cnt[op])
        max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
        f = fc.And([
            fc.And(max_rvars),
            fc.And(lconds),
            fc.And(rconds),
        ])
        #print(f.serialize())
        for sol in smt_solve_all(f.to_hwtypes().value, opts):
            r_cnt = {}
            for ri, rvar in rvars.items():
                assert rvar.value in sol
                rval = _to_int(sol[rvar.value])
                if rval != 0:
                    r_cnt[ri] = rval
            print("RCNT", r_cnt,flush=True)
            #lhs_pats = [(self.rdb.rules[ri].lhs, cnt) for ri, cnt in r_cnt.items()]
            mset = []
            lhs_sol_ops = []
            rhs_sol_ops = []
            for ri, cnt in r_cnt.items():
                rule = poss_rules[ri]
                mset.append((rule, cnt))
                for op in rule.lhs.ops:
                    lhs_sol_ops += [op]*cnt
                for op in rule.rhs.ops:
                    rhs_sol_ops += [op]*cnt
                
            lhs_sol_op_cnts = {}
            for op in lhs_sol_ops:
                lhs_sol_op_cnts[op.qualified_name] = lhs_sol_op_cnts.get(op.qualified_name, 0) + 1
            rhs_sol_op_cnts = {}
            for op in rhs_sol_ops:
                rhs_sol_op_cnts[op.qualified_name] = rhs_sol_op_cnts.get(op.qualified_name, 0) + 1

            if ((lhs_sol_op_cnts == lhs_op_cnt or any((isinstance(op.comb,BVDontCare) or isinstance(op.comb,CBVDontCare)) for op in lhs_sol_ops)) and
                (rhs_sol_op_cnts == rhs_op_cnt or any((isinstance(op.comb,BVDontCare) or isinstance(op.comb,CBVDontCare)) for op in rhs_sol_ops))):
                yield mset

    def is_new_pat(self, pat: Pattern, epats: tp.List[Pattern]):
        new_pat = True
        for epat in epats:
            eq = epat.equal(pat)
            if eq:
                assert pat.equal(pat)
                print("EQUAL PAT", flush=True)
                new_pat = False
                break
        return new_pat

    def is_new_rule(self, rule, erules):
        for erule in erules:
            eq = erule.equal(rule)
            if eq:
                assert rule.equal(erule)
                print("EQUAL RULE", flush=True)
                return False
        return True

    def synth_T_to_op_list(self, synth_T):
        op_list = []
        BV = GlobalModules['bv']
        for T in synth_T:
            assert T.const
            op = BV._synth_const[T.n]
            #TODO: this is a temporary fix to speed things up for PEs
            if T.n == 16:
                op.constraints = lambda in_lvars,out_lvars,in_vars,out_vars: out_vars[0] == 0
            op_list.append(op)

        return op_list

    def dont_care_T_to_op_list(self, dont_care_T):
        op_list = []
        BV = GlobalModules['bv']
        for T in dont_care_T:
            if T.const:
                op = BV.c_dont_care[T.n]
            else:
                op = BV.dont_care[T.n]
            op_list.append(op)

        return op_list

    def gen_all_rules(self, E_opts, ir_opts, narrow_opts, max_outputs=None, opts=SolverOpts(), bin_search_dont_cares = False):
        LC, E, comp = E_opts
        assert not LC
        ruleid = 0
        for lN in range(1, self.maxL+1):
            lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
            for lhs_ids in multicomb(lhs_mc_ids, lN):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                #lhs_op_names = [op.qualified_name for op in lhs_ops]
                for rN in range(1, self.maxR+1):
                    rhs_mc_ids = flat([[i for _ in range(self.opMaxR[i])] for i in range(len(self.rhss))])
                    for rhs_ids in multicomb(rhs_mc_ids, rN):
                        rhs_ops = [self.rhss[i] for i in rhs_ids]
                        #rhs_op_names = [op.qualified_name for op in rhs_ops]
                        kstr = "("+",".join(str(i) for i in lhs_ids) + ")"
                        kstr += "("+",".join(str(i) for i in rhs_ids) + ")"
                        if opts.log:
                            print(kstr,flush=True)
                            print_kind(lhs_ids, rhs_ids)

                        for (lhs_dont_care_T, rhs_dont_care_T) in self.all_dont_care_T(lhs_ops, rhs_ops):
                            for (iT, oT) in self.allT(lhs_ops, rhs_ops, lhs_dont_care_T, rhs_dont_care_T, max_outputs):
                                for (lhs_synth_T, rhs_synth_T) in self.all_synth_T(iT, oT, lhs_ops, rhs_ops, lhs_dont_care_T, rhs_dont_care_T):
                                    if not self.valid_program_components(iT, oT, lhs_ops, rhs_ops, lhs_synth_T, rhs_synth_T, lhs_dont_care_T, rhs_dont_care_T):
                                        continue

                                    lhs_synth_ops = self.synth_T_to_op_list(lhs_synth_T)
                                    rhs_synth_ops = self.synth_T_to_op_list(rhs_synth_T)
                                    lhs_dont_care_ops = self.dont_care_T_to_op_list(lhs_dont_care_T)
                                    rhs_dont_care_ops = self.dont_care_T_to_op_list(rhs_dont_care_T)
                                    lhs_ops_all = lhs_ops + lhs_synth_ops + lhs_dont_care_ops
                                    rhs_ops_all = rhs_ops + rhs_synth_ops + rhs_dont_care_ops

                                    new_rules = []
                                    k = (tuple(lhs_ids), tuple(rhs_ids), iT, oT, tuple(lhs_synth_T), tuple(rhs_synth_T))
                                    if opts.log:
                                        print_iot(iT, oT)
                                    rs = RuleSynth(
                                        iT,
                                        oT,
                                        lhs_op_list=lhs_ops_all,
                                        rhs_op_list=rhs_ops_all,
                                        ir_opts=ir_opts,
                                        narrow_opts=narrow_opts,
                                        pat_en_t=self.pat_en_t,
                                        simplify_dont_cares = self.simplify_dont_cares,
                                        simplify_gen_consts = self.simplify_gen_consts,
                                    )
                                    existing_rules = []
                                    existing_mappings = []
                                    start = timeit.default_timer()
                                    for mset in self.all_composite_msets(lhs_ids, rhs_ids, iT, oT, lhs_synth_ops, rhs_synth_ops, opts):
                                        lhs_pats = flat([[rule.lhs for _ in range(cnt)] for rule, cnt in mset])
                                        rhs_pats = flat([[rule.rhs for _ in range(cnt)] for rule, cnt in mset])
                                        lhs_dags = enum_dags(iT, oT, lhs_pats)
                                        rhs_dags = enum_dags(iT, oT, rhs_pats)
                                        for lhs_dag,rhs_dag in it.product(lhs_dags, rhs_dags):
                                            lhs_composite_pats = composite_pat(iT, oT, lhs_dag, lhs_pats, lhs_ops_all)
                                            rhs_composite_pats = composite_pat(iT, oT, rhs_dag, rhs_pats, rhs_ops_all)
                                            for (l_pat,l_mapping),(r_pat,r_mapping) in it.product(lhs_composite_pats, rhs_composite_pats):
                                                existing_rules.append(Rule(l_pat, r_pat, 0, 0))
                                                existing_mappings.append((l_mapping, r_mapping))

                                    comp_time = timeit.default_timer() - start
                                    if len(existing_rules) > 0 and opts.log:
                                        print("CMPTIME", round(comp_time,3), flush=True)
                                    if comp:
                                        for crule,(l_map, r_map) in zip(existing_rules, existing_mappings):
                                            rule_cond, enum_time = rs.ruleL(crule,l_map,r_map)
                                            comp_time += enum_time
                                            rs.synth_base = rs.synth_base & ~rule_cond
                                    sat_time = []
                                    if bin_search_dont_cares:
                                        rulegen = rs.CEGISAll_bin_search
                                    else:
                                        rulegen = rs.CEGISAll
                                    
                                    for rule in rulegen(E, LC, opts):
                                        sat_time.append(rule.time)
                                        assert rule.verify()
                                        if self.is_new_rule(rule, existing_rules):
                                            rule.id = ruleid
                                            ruleid += 1
                                            new_rules.append(rule)
                                            existing_rules.append(rule)
                                            yield rule
                                    enum_time = sum(rs.enum_times)
                                    times = (sat_time, comp_time, enum_time)
                                    if sum(sat_time) > 0.0001:
                                        self.rdb.add_rules(k, new_rules, times)
                                    else:
                                        assert len(new_rules) == 0

    # Finds all combinations of rules that exactly match the lhs and rhs
    def all_lc_composite_msets(self, lhs_ids, cur_cost, iT, oT, lhs_synth_ops, opts:SolverOpts):
        NI = len(iT)
        NO = len(oT)
        lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])

        for op in lhs_synth_ops:
            lhs_op_cnt[op.qualified_name] = lhs_op_cnt.get(op.qualified_name, 0) + 1
        
        #Prefiltering
        poss_pats = {}
        #ri_N = {}
        ri_to_k = {}
        for ri, (k, i, rule) in enumerate(self.rdb.enum_rules()):
            ri_to_k[ri] = (k, i)
            l_eq = rule.lhs.op_cnt == lhs_op_cnt
            if l_eq and rule.cost <= cur_cost and rule.NI >= NI and rule.NO >= NO:
                if opts.log:
                    print(f"R1", {ri:1}, end=", ")
                yield [(rule.lhs, 1)]
                continue
            l_subseteq = _m_subseteq(rule.lhs.op_cnt_no_dont_cares, lhs_op_cnt)
            if l_subseteq:
                poss_pats[ri] = (rule.lhs, rule.cost)
                #ri_N[ri] = (I_max(rule.lhs.ops), I_max(rule.rhs.ops))
        if len(poss_pats) == 0:
            return
        #Early out if there is not at least one matching op over all poss rules
        #poss_ops = functools.reduce(lambda s0, s1: s0|s1, [set(op_cnt.keys()) for op_cnt,_,_ in poss_rules.values()])
        #if poss_ops != set(lhs_op_cnt.keys()):
        #    return

        rvarT = ht.SMTBitVector[32]
        max_rvar = max(cnt for cnt in lhs_op_cnt.values())
        lhs_op_cnts = {op:rvarT(0) for op in lhs_op_cnt.keys()}
        rvars = {ri:get_var(f"R{ri}", 32) for ri in poss_pats.keys()}
        tot_cost = rvarT(0)
        for ri, (pat, cost) in poss_pats.items():
            rvar = rvars[ri]

            #ir cnt
            for op, cnt in pat.op_cnt_no_dont_cares.items():
                assert op in lhs_op_cnts
                lhs_op_cnts[op] += rvar*cnt
            #cost
            tot_cost += rvar*cost


        lconds = []
        for op, cnt in lhs_op_cnts.items():
            lconds.append(cnt <= lhs_op_cnt[op])
        cost_cond = (tot_cost <= cur_cost)
        max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
        f = fc.And([
            fc.And(max_rvars),
            fc.And(lconds),
            cost_cond,
        ])
        #print(f.serialize())
        for sol in smt_solve_all(f.to_hwtypes().value, opts):
            r_cnt = {}
            for ri, rvar in rvars.items():
                assert rvar.value in sol
                rval = _to_int(sol[rvar.value])
                if rval != 0:
                    r_cnt[ri] = rval
            if opts.log:
                print("RM", r_cnt, end=", ")
            #lhs_pats = [(self.rdb.rules[ri].lhs, cnt) for ri, cnt in r_cnt.items()]
            mset = []
            sol_ops = []
            for ri, cnt in r_cnt.items():
                pat, rcost = poss_pats[ri]
                mset.append((pat, cnt))
                for op in pat.ops:
                    sol_ops += [op]*cnt

            sol_op_cnts = {}
            for op in sol_ops:
                sol_op_cnts[op.qualified_name] = sol_op_cnts.get(op.qualified_name, 0) + 1

            if sol_op_cnts == lhs_op_cnt:
                yield mset
            else:
                if any((isinstance(op.comb,BVDontCare) or isinstance(op.comb,CBVDontCare)) for op in sol_ops):
                    yield mset


    #Returns the order of rhs ids sorted by cost
    def gen_rhs_order(self, costs):
        def cmp(v1, v2):
            c1, ids1 = v1
            c2, ids2 = v2
            if c1 < c2:
                return -1
            elif c1 > c2:
                return 1
            if len(ids1) < len(ids2):
                return -1
            elif len(ids1) > len(ids2):
                return 1
            u1 = len(set(ids1))
            u2 = len(set(ids2))
            if u1 < u2:
                return 1
            else:
                return -1


        rs = []
        for rN in range(1, self.maxR+1):
            rhs_mc_ids = flat([[i for _ in range(self.opMaxR[i])] for i in range(len(self.rhss))])
            for rhs_ids in multicomb(rhs_mc_ids, rN):
                cost = sum(costs[i] for i in rhs_ids)
                rs.append((cost,rhs_ids))
        return [tuple(rhs_ids) for _, rhs_ids in sorted(rs, key=functools.cmp_to_key(cmp))]

    def gen_lowcost_rules(self, E_opts, ir_opts, narrow_opts, costs, max_outputs = None, opts=SolverOpts(), bin_search_dont_cares = False):
        LC, E, comp = E_opts
        assert len(costs)==len(self.rhss)
        rhs_id_order = self.gen_rhs_order(costs)
        for lN in range(1, self.maxL+1):
            lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
            for lhs_ids in multicomb(lhs_mc_ids, lN):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                for rhs_ids in rhs_id_order:
                    rhs_ops = [self.rhss[i] for i in rhs_ids]
                    kstr = "("+",".join(str(i) for i in lhs_ids) + ")"
                    kstr += "("+",".join(str(i) for i in rhs_ids) + ")"
                    if opts.log:
                        print(kstr,flush=True)
                    cur_cost = sum(costs[rid] for rid in rhs_ids)
                    for (lhs_dont_care_T, rhs_dont_care_T) in self.all_dont_care_T(lhs_ops, rhs_ops):
                        for (iT, oT) in self.allT(lhs_ops, rhs_ops, lhs_dont_care_T, rhs_dont_care_T, max_outputs):
                            for (lhs_synth_T, rhs_synth_T) in self.all_synth_T(iT, oT, lhs_ops, rhs_ops, lhs_dont_care_T, rhs_dont_care_T):
                                if not self.valid_program_components(iT, oT, lhs_ops, rhs_ops, lhs_synth_T, rhs_synth_T, lhs_dont_care_T, rhs_dont_care_T):
                                    continue

                                lhs_synth_ops = self.synth_T_to_op_list(lhs_synth_T)
                                rhs_synth_ops = self.synth_T_to_op_list(rhs_synth_T)
                                lhs_dont_care_ops = self.dont_care_T_to_op_list(lhs_dont_care_T)
                                rhs_dont_care_ops = self.dont_care_T_to_op_list(rhs_dont_care_T)
                                lhs_ops_all = lhs_ops + lhs_synth_ops + lhs_dont_care_ops
                                rhs_ops_all = rhs_ops + rhs_synth_ops + rhs_dont_care_ops

                                new_rules = []
                                k = (tuple(lhs_ids), tuple(rhs_ids), iT, oT, 
                                     tuple(lhs_synth_T), tuple(rhs_synth_T), 
                                     tuple(lhs_dont_care_T), tuple(rhs_dont_care_T))

                                #kstr += f":{NI}"
                                if opts.log:
                                    print_iot(iT, oT)
                                rs = RuleSynth(
                                    iT,
                                    oT,
                                    lhs_op_list=lhs_ops_all,
                                    rhs_op_list=rhs_ops_all,
                                    ir_opts=ir_opts,
                                    narrow_opts=narrow_opts,
                                    pat_en_t=self.pat_en_t,
                                    simplify_dont_cares = self.simplify_dont_cares,
                                    simplify_gen_consts = self.simplify_gen_consts,
                                )
                                existing_pats = []
                                op_mappings = []
                                start = timeit.default_timer()
                                for mset in self.all_lc_composite_msets(lhs_ids, cur_cost, iT, oT, lhs_synth_ops, opts):
                                    lhs_pats = flat([[pat for _ in range(cnt)] for pat, cnt in mset])
                                    dags = enum_dags(iT, oT, lhs_pats)
                                    for dag in dags:
                                        for lhs_pat,op_mapping in composite_pat(iT, oT, dag, lhs_pats, lhs_ops_all):
                                            existing_pats.append(lhs_pat)
                                            op_mappings.append(op_mapping)
                                comp_time = timeit.default_timer() - start
                                if comp:
                                    for cpat,op_mapping in zip(existing_pats, op_mappings):
                                        pat_cond, enum_time = rs.patL(cpat, op_mapping)
                                        comp_time += enum_time
                                        rs.synth_base = rs.synth_base & ~pat_cond
                                sat_time = []
                                if bin_search_dont_cares:
                                    rulegen = rs.CEGISAll_bin_search
                                else:
                                    rulegen = rs.CEGISAll
                                
                                for rule in rulegen(E, LC, opts):
                                    rule.cost = cur_cost
                                    sat_time.append(rule.time)
                                    assert rule.verify()
                                    if self.is_new_pat(rule.lhs, existing_pats):
                                        new_rules.append(rule)
                                        existing_pats.append(rule.lhs)
                                        yield rule
                                enum_time = sum(rs.enum_times)
                                times = (sat_time, comp_time, enum_time)
                                if len(new_rules)>0 or sum(sat_time) > 0.0001:
                                    self.rdb.add_rules(k, new_rules, times)
                                else:
                                    assert len(new_rules) == 0








    #def enum_buckets(self):
    #    rhs_id_order = self.gen_rhs_order()
    #    for lN in range(1, self.maxL+1):
    #        lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
    #        for lhs_ids in multicomb(lhs_mc_ids, lN):
    #            lhs_ops = [self.lhss[i] for i in lhs_ids]
    #            for rhs_ids in rhs_id_order:
    #                rhs_ops = [self.rhss[i] for i in rhs_ids]
    #                if self.custom_filter(lhs_ids, rhs_ids):
    #                    continue
    #                for (iT, oT) in self.gen_all_T2(lhs_ops, rhs_ops):
    #                    k = (lhs_ids, rhs_ids, iT, oT)
    #                    yield k


    #def num_queries(self):
    #    return sum(1 for _ in self.enum_buckets())

    #def gen_all_T1(self, ops):
    #    def get_cnt(op, k):
    #        return {T:len(ids) for T, ids in types_to_nTs(op.get_type()[k]).items()}

    #    def count(l):
    #        ret = {}
    #        for d in l:
    #            for n, v in d.items():
    #                ret[n] = ret.get(n, 0) + v
    #        return ret

    #    iTs = count([get_cnt(op, 0) for op in ops])
    #    oTs = count([get_cnt(op, 1) for op in ops])
    #    if len(oTs) > 1:
    #        raise NotImplementedError()
    #    max_oT = {T:1 for T in oTs.keys()}
    #    max_iT = {T:(cnt-(oTs.get(T,0) - max_oT.get(T, 0))) for T,cnt in iTs.items()}


    #    #There is a partial order of input types. It forms a lattice.
    #    #I need to return a full group where each group is equal
    #    i_poss = {T:list(reversed(range(1,m+1))) for T,m in max_iT.items()}
    #    o_poss = {T:list(reversed(range(1,m+1))) for T,m in max_oT.items()}
    #    ivss = [(sum(ivs),ivs) for ivs in it.product(*list(i_poss.values()))]
    #    grouped_ivs = {}
    #    for (s, ivs) in ivss:
    #        grouped_ivs.setdefault(s,[]).append(ivs)
    #    for s, ivss in sorted(grouped_ivs.items()):
    #        print(s)
    #        group = []
    #        for ivs in ivss:
    #            iT = []
    #            for T, v in zip(i_poss.keys(), ivs):
    #                iT += [T for _ in range(v)]
    #            for ovs in it.product(*list(o_poss.values())):
    #                oT = []
    #                for T, v in zip(o_poss.keys(), ovs):
    #                    oT += [T for _ in range(v)]
    #                assert len(oT) == 1
    #                group.append((tuple(iT), tuple(oT)))
    #        yield group

    ## Finds all combinations of rules that exactly match the lhs and have less cost than or eq to the rhs
    #def all_rule_covers(self, lhs_ids, rhs_ids, iT, oT):
    #    exp_cost = sum([self.costs[ri] for ri in rhs_ids])
    #    assert isinstance(exp_cost, int)
    #    iTs = _list_to_counts(iT)
    #    oTs = _list_to_counts(oT)
    #    lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])
    #    #Prefiltering
    #    poss_rules = {}
    #    for ri, (rule, ri_cost) in enumerate(zip(self.rdb.rules, self.rdb.costs)):
    #        if ri_cost > exp_cost:
    #            continue
    #        elif rule.lhs.op_cnt == lhs_op_cnt:
    #            rule_iTs = _list_to_counts(rule.lhs.iT)
    #            if all(rule_iTs.get(T,0) >=cnt for T, cnt in iTs.items()):
    #                print("RCNT", {ri:1},flush=True)
    #                yield [(rule.lhs, 1)]
    #            #yield [(rule.lhs, 1)]
    #        elif set(lhs_op_cnt.keys()) >= set(rule.lhs.op_cnt.keys()):
    #            if all([rule.lhs.op_cnt.get(op, 0) <= cnt for op, cnt in lhs_op_cnt.items()]):
    #                #Check that typing works
    #                poss_rules[ri] = (rule.lhs.op_cnt, (rule.lhs.iT, rule.lhs.oT), ri_cost)
    #    if len(poss_rules) == 0:
    #        return

    #    #Early out if there is not at least one matching op over all poss rules
    #    poss_ops = functools.reduce(lambda s0, s1: s0|s1, [set(op_cnt.keys()) for op_cnt,_,_ in poss_rules.values()])
    #    if poss_ops != set(lhs_op_cnt.keys()):
    #        return


    #    rvarT = ht.SMTBitVector[32]
    #    max_rvar = max(cnt for cnt in lhs_op_cnt.values())
    #    lhs_op_cnts = {op:rvarT(0) for op in lhs_op_cnt.keys()}
    #    cost = rvarT(0)
    #    rvars = {ri:get_var(f"R{ri}", 32) for ri in poss_rules.keys()}
    #    lhs_iTs = {}
    #    lhs_oTs = {}
    #    for ri, (op_cnt, (r_iT, r_oT), ri_cost) in poss_rules.items():
    #        rvar = rvars[ri]
    #        #Cost
    #        cost += rvar*ri_cost

    #        #op count is good
    #        for op, cnt in op_cnt.items():
    #            assert op in lhs_op_cnts
    #            lhs_op_cnts[op] += rvar*cnt

    #        #Typing is good
    #        for T, cnt in _list_to_counts(r_iT).items():
    #            v = lhs_iTs.get(T,rvarT(0))
    #            lhs_iTs[T] = v + rvar*cnt
    #        for T, cnt in _list_to_counts(r_oT).items():
    #            v = lhs_oTs.get(T,rvarT(0))
    #            lhs_oTs[T] = v + rvar*cnt

    #    #Using lhs_oTs is a bit of a hack. This is assuming that rules only have 1 output
    #    max_lhs_oT = lhs_oTs
    #    max_lhs_iT = {T:(cnt-(lhs_oTs.get(T,0) - max_lhs_oT.get(T, 0))) for T,cnt in lhs_iTs.items()}
    #    iT_conds = []
    #    for T, cnt in iTs.items():
    #        iT_conds.append(max_lhs_iT[T] >= cnt)
    #    lconds = []
    #    for op, cnt in lhs_op_cnts.items():
    #        lconds.append(cnt == lhs_op_cnt[op])
    #    max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
    #    f = fc.And([
    #        fc.And(max_rvars),
    #        fc.And(lconds),
    #        fc.And(iT_conds),
    #        cost <= exp_cost
    #    ])
    #    for sol in smt_solve_all(f.to_hwtypes().value):
    #        r_cnt = {}
    #        for ri, rvar in rvars.items():
    #            assert rvar.value in sol
    #            rval = _to_int(sol[rvar.value])
    #            if rval != 0:
    #                r_cnt[ri] = rval
    #        print("RCNT", r_cnt,flush=True)
    #        lhs_pats = [(self.rdb.rules[ri].lhs, cnt) for ri, cnt in r_cnt.items()]
    #        yield lhs_pats

    #def get_ir_const(self, opts):
    #    if isinstance(self.const_synth, str):
    #        #Load from file
    #        raise NotImplementedError()
    #    assert isinstance(self.const_synth, bool)
    #    if self.const_synth:
    #        cd = ConstDiscover(self.lhss, self.maxL, self.opMaxL, self.pat_en_t, self.sym_opts)
    #        return cd.gen_all(self.const_vals, opts=opts)
    #    else:
    #        return ({}, {}), []

    #def gen_all_lc(self, opts=SolverOpts()):
    #    (ea_pats, const_specs), id_pats = self.get_ir_const(opts)
    #    lhs_exclude_pats = [id_pats] + list(ea_pats.values())
    #    #Update lhss
    #    self.lhss += list(const_specs.values())
    #    rhs_id_order = self.gen_rhs_order()
    #    for lN in range(1, self.maxL+1):
    #        lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
    #        for lhs_ids in multicomb(lhs_mc_ids, lN):
    #            lhs_ops = [self.lhss[i] for i in lhs_ids]
    #            lhs_op_cnt = _list_to_counts([op.qualified_name for op in lhs_ops])
    #            exclude_pats = []
    #            for pats in lhs_exclude_pats:
    #                for pat in pats:
    #                    if ge0_cnts(sub_cnts(lhs_op_cnt, pat.op_cnt)):
    #                        exclude_pats.append(pat)
    #            print(f"Excluded Bad Patterns: {len(exclude_pats)}")
    #            for rhs_ids in rhs_id_order:
    #                rhs_ops = [self.rhss[i] for i in rhs_ids]
    #                if opts.log:
    #                    print_kind(lhs_ids, rhs_ids)
    #                for (iT, oT) in self.gen_all_T2(lhs_ops, rhs_ops):
    #                    k = (lhs_ids, rhs_ids, iT, oT)
    #                    if opts.log:
    #                        print_iot(iT, oT)
    #                    if self.custom_filter(lhs_ids, rhs_ids):
    #                        continue

    #                    #Discover all lhs pattern covers
    #                    if self.pgf:
    #                        cstart = timeit.default_timer()
    #                        covers = list(self.all_rule_covers(lhs_ids, rhs_ids, iT, oT))
    #                        ct = timeit.default_timer() - cstart
    #                        self.rdb.add_cover_time(k, ct)
    #                    else:
    #                        covers = []

    #                    info = ((tuple(lhs_ids), tuple(rhs_ids)), (iT, oT))
    #                    rs = RuleSynth(
    #                        iT,
    #                        oT,
    #                        lhs_op_list=lhs_ops,
    #                        rhs_op_list=rhs_ops,
    #                        pat_en_t=self.pat_en_t,
    #                        sym_opts=self.sym_opts,
    #                        only_lhs_sym=self.only_lhs_sym,
    #                    )
    #                    assert rs.lhs_cs.types_viable and rs.rhs_cs.types_viable
    #                    for cover in covers:
    #                        rs.add_rule_cover(cover)
    #                    for pat in exclude_pats:
    #                        rs.exclude_pattern(pat)
    #                    for i, (sol, t) in enumerate(rs.cegis_all(opts)):
    #                        lhs_pat = rs.lhs_cs.pattern_from_sol(sol)
    #                        rhs_pat = rs.rhs_cs.pattern_from_sol(sol)
    #                        rule = Rule(i, lhs_pat, rhs_pat, t, info)
    #                        assert rule.verify()
    #                        rule_cost = sum([self.costs[self.rhs_name_to_id[op]]*cnt for op, cnt in rule.rhs.op_cnt.items()])
    #                        self.rdb.add_rule(rule, rule_cost)
    #                        yield rule
    #                        #Force the new cover to be used in the current it
    #                        #Recalculate the covers generator for other Types
    #                        if self.igf:
    #                            cur_cover = [(lhs_pat, 1)]
    #                            rs.add_rule_cover(cur_cover)
    #                            covers.append(cur_cover)
