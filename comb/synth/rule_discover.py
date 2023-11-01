import functools
import timeit

from comb import Comb
from comb.frontend.ast import TypeCall, BVType, IntValue
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

    def allT(self, lhs_ops, rhs_ops, max_outputs = 1):
        # generate all possible program input and output type combinations
        assert max_outputs == 1

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)

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
                for num_in in range(max_inputs, 0, -1):
                    for iTs_sel in multicomb(iTs_all, num_in):
                        yield (tuple(iTs_sel), tuple(oTs_sel))


    def valid_program_components(self, iT, oT, lhs_ops, rhs_ops):
        # return True if the program components could possibly form a valid program
        # else return False

        # TODO: could make this a more elaborate check in the future if too many
        # hopeless programs make it past this check and slow down the synthesis

        lop_iTs, lop_oTs = T_count(lhs_ops)
        rop_iTs, rop_oTs = T_count(rhs_ops)

        lsrcs_no_i = set(lop_oTs.keys())
        rsrcs_no_i = set(rop_oTs.keys())
        lsncs_no_o = set(lop_iTs.keys())
        rsncs_no_o = set(rop_iTs.keys())

        #all non-output sncs must have a src
        if not lsncs_no_o <= (set(iT) | lsrcs_no_i) or not rsncs_no_o <= (set(iT) | rsrcs_no_i):
            return False

        #all outputs must have a non-input src
        if not set(oT) <= lsrcs_no_i or not set(oT) <= rsrcs_no_i:
            return False

        return True

    # Finds all combinations of rules that exactly match the lhs and rhs
    def all_composite_msets(self, lhs_ids, rhs_ids, iT, opts:SolverOpts):
        NI = len(iT)
        lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])
        rhs_op_cnt = _list_to_counts([self.rhss[rid].qualified_name for rid in rhs_ids])

        #Prefiltering
        poss_rules = {}
        #ri_N = {}
        ri_to_k = {}
        for ri, (k, i, rule) in enumerate(self.rdb.enum_rules()):
            ri_to_k[ri] = (k, i)
            l_eq = rule.lhs.op_cnt == lhs_op_cnt
            r_eq = rule.rhs.op_cnt == rhs_op_cnt
            if l_eq and r_eq and rule.NI >= NI:
                if opts.log:
                    print("RCNT", {ri:1},flush=True)
                yield [(rule, 1)]
                continue
            l_subseteq = _m_subseteq(rule.lhs.op_cnt, lhs_op_cnt)
            r_subseteq = _m_subseteq(rule.rhs.op_cnt, rhs_op_cnt)
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
        l_NI, l_NO = rvarT(0), rvarT(0)
        for ri, rule in poss_rules.items():
            rvar = rvars[ri]

            #ir cnt
            for op, cnt in rule.lhs.op_cnt.items():
                assert op in lhs_op_cnts
                lhs_op_cnts[op] += rvar*cnt
            #isa cnt
            for op, cnt in rule.rhs.op_cnt.items():
                if op not in rhs_op_cnts:
                    raise ValueError
                assert op in rhs_op_cnts
                rhs_op_cnts[op] += rvar*cnt

            l_NI += rvar*len(rule.iT)
            l_NO += rvar

        N_cond = (l_NI - l_NO + 1 >= NI)
        lconds = []
        for op, cnt in lhs_op_cnts.items():
            lconds.append(cnt == lhs_op_cnt[op])
        rconds = []
        for op, cnt in rhs_op_cnts.items():
            rconds.append(cnt == rhs_op_cnt[op])
        max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
        f = fc.And([
            fc.And(max_rvars),
            N_cond,
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
            for ri, cnt in r_cnt.items():
                rule = poss_rules[ri]
                mset.append((rule, cnt))
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
        new_rule = True
        for erule in erules:
            eq = erule.equal(rule)
            if eq:
                assert rule.equal(erule)
                print("EQUAL RULE", flush=True)
                #print("NEW")
                #print(rule)
                #print("="*100)
                #print("OLD")
                #print(erule)
                #print("END EQUAL RULE")
                new_rule = False
                #erule.update_time(rule.time)
                #erule.add_equiv(rule)
                break
        return new_rule

    def gen_all_rules(self, E_opts, ir_opts, narrow_opts, opts=SolverOpts()):
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
                        for (iT, oT) in self.allT(lhs_ops, rhs_ops):
                            if not self.valid_program_components(iT, oT, lhs_ops, rhs_ops):
                                continue
                            new_rules = []
                            NI = len(iT)
                            k = (tuple(lhs_ids), tuple(rhs_ids), iT)
                            if opts.log:
                                print_iot(iT, oT)
                            rs = RuleSynth(
                                iT,
                                oT,
                                lhs_op_list=lhs_ops,
                                rhs_op_list=rhs_ops,
                                ir_opts=ir_opts,
                                narrow_opts=narrow_opts,
                                pat_en_t=self.pat_en_t,
                            )
                            existing_rules = []
                            start = timeit.default_timer()
                            for mset in self.all_composite_msets(lhs_ids, rhs_ids, iT, opts):
                                lhs_pats = flat([[rule.lhs for _ in range(cnt)] for rule, cnt in mset])
                                rhs_pats = flat([[rule.rhs for _ in range(cnt)] for rule, cnt in mset])
                                dags = enum_dags(NI, lhs_pats)
                                for dag in dags:
                                    lhs_pat = composite_pat(iT, oT, dag, lhs_pats, lhs_ops)
                                    rhs_pat = composite_pat(iT, oT, dag, rhs_pats, rhs_ops)
                                    existing_rules.append(Rule(lhs_pat, rhs_pat, 0, 0))
                            comp_time = timeit.default_timer() - start
                            if len(existing_rules) > 0 and opts.log:
                                print("CMPTIME", round(comp_time,3), flush=True)
                            if comp:
                                for crule in existing_rules:
                                    rule_cond, enum_time = rs.ruleL(crule)
                                    comp_time += enum_time
                                    rs.query = rs.query & ~rule_cond
                            sat_time = []
                            for rule in rs.CEGISAll(E, LC, opts):
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
    def all_lc_composite_msets(self, lhs_ids, cur_cost, iT, opts:SolverOpts):
        NI = len(iT)
        lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])
        #rhs_op_cnt = _list_to_counts([self.rhss[rid].qualified_name for rid in rhs_ids])

        #Prefiltering
        poss_pats = {}
        #ri_N = {}
        ri_to_k = {}
        for ri, (k, i, rule) in enumerate(self.rdb.enum_rules()):
            ri_to_k[ri] = (k, i)
            l_eq = rule.lhs.op_cnt == lhs_op_cnt
            if l_eq and rule.cost <= cur_cost and rule.NI >= NI:
                print(f"R1", {ri:1}, end=", ")
                yield [(rule.lhs, 1)]
                continue
            l_subseteq = _m_subseteq(rule.lhs.op_cnt, lhs_op_cnt)
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
        l_NI, l_NO = rvarT(0), rvarT(0)
        tot_cost = rvarT(0)
        for ri, (pat, cost) in poss_pats.items():
            rvar = rvars[ri]

            #ir cnt
            for op, cnt in pat.op_cnt.items():
                assert op in lhs_op_cnts
                lhs_op_cnts[op] += rvar*cnt
            #cost
            tot_cost += rvar*cost

            l_NI += rvar*pat.NI
            l_NO += rvar

        N_cond = (l_NI - l_NO + 1 >= NI)
        lconds = []
        for op, cnt in lhs_op_cnts.items():
            lconds.append(cnt == lhs_op_cnt[op])
        cost_cond = (tot_cost <= cur_cost)
        max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
        f = fc.And([
            fc.And(max_rvars),
            N_cond,
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
            print("RM", r_cnt, end=", ")
            #lhs_pats = [(self.rdb.rules[ri].lhs, cnt) for ri, cnt in r_cnt.items()]
            mset = []
            for ri, cnt in r_cnt.items():
                pat, rcost = poss_pats[ri]
                mset.append((pat, cnt))
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

    def gen_lowcost_rules(self, E_opts, ir_opts, narrow_opts, costs, opts=SolverOpts()):
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
                    for (iT, oT) in self.allT(lhs_ops, rhs_ops):
                        if not self.valid_program_components(iT, oT, lhs_ops, rhs_ops):
                            continue
                        new_rules = []
                        NI = len(iT)
                        k = (tuple(lhs_ids), tuple(rhs_ids), iT)

                        #kstr += f":{NI}"
                        if opts.log:
                            print_iot(iT, oT)
                        rs = RuleSynth(
                            iT,
                            oT,
                            lhs_op_list=lhs_ops,
                            rhs_op_list=rhs_ops,
                            ir_opts=ir_opts,
                            narrow_opts=narrow_opts,
                            pat_en_t=self.pat_en_t,
                        )
                        existing_pats = []
                        start = timeit.default_timer()
                        for mset in self.all_lc_composite_msets(lhs_ids, cur_cost, iT, opts):
                            lhs_pats = flat([[pat for _ in range(cnt)] for pat, cnt in mset])
                            dags = enum_dags(NI, lhs_pats)
                            for dag in dags:
                                lhs_pat = composite_pat(iT, oT, dag, lhs_pats, lhs_ops)
                                existing_pats.append(lhs_pat)
                        comp_time = timeit.default_timer() - start
                        if comp:
                            if LC:
                                for cpat in existing_pats:
                                    pat_cond, enum_time = rs.patL(cpat)
                                    comp_time += enum_time
                                    rs.query = rs.query & ~pat_cond
                            else:
                                erules = []
                                for mset in self.all_composite_msets(lhs_ids, rhs_ids, iT, opts):
                                    lhs_pats = flat([[rule.lhs for _ in range(cnt)] for rule, cnt in mset])
                                    rhs_pats = flat([[rule.rhs for _ in range(cnt)] for rule, cnt in mset])
                                    dags = enum_dags(NI, lhs_pats)
                                    for dag in dags:
                                        lhs_pat = composite_pat(iT, oT, dag, lhs_pats, lhs_ops)
                                        rhs_pat = composite_pat(iT, oT, dag, rhs_pats, rhs_ops)
                                        erules.append(Rule(lhs_pat, rhs_pat, 0, 0))
                                for crule in erules:
                                    rule_cond, enum_time = rs.ruleL(crule)
                                    rs.query = rs.query & ~rule_cond
                        sat_time = []
                        for rule in rs.CEGISAll(E, LC, opts):
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
