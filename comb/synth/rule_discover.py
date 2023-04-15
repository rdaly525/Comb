import functools

from comb import Comb
from comb.frontend.ast import TypeCall, BVType, IntValue
from comb.synth.pattern import PatternEncoding, SymOpts
from comb.synth.rule import Rule, RuleDatabase
from comb.synth.rule_synth import RuleSynth
from comb.synth.solver_utils import SolverOpts, smt_solve_all, get_var
from comb.synth.utils import _list_to_counts, flat, _to_int, comb_type_to_nT, _list_to_dict

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

@dataclass
class RuleDiscovery:
    lhss: tp.List[Comb]
    rhss: tp.List[Comb]
    costs: tp.List[int]
    maxL: int
    maxR: int
    pat_en_t: tp.Type[PatternEncoding]
    sym_opts: SymOpts
    opMaxL: tp.Mapping[int, int] = None
    opMaxR: tp.Mapping[int, int] = None
    custom_filter: tp.Callable = lambda x,y: False
    pgf: bool = True #Preemtive Generative Filtering
    igf: bool = True #Incremental Generative Filtering

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
        assert len(self.costs) == len(self.rhss)

    #Returns the order of rhs ids sorted by cost
    def gen_rhs_order(self):
        rs = []
        for rN in range(1, self.maxR+1):
            rhs_mc_ids = flat([[i for _ in range(self.opMaxR[i])] for i in range(len(self.rhss))])
            for rhs_ids in multicomb(rhs_mc_ids, rN):
                cost = sum(self.costs[i] for i in rhs_ids)
                rs.append((cost,rhs_ids))
        return [tuple(rhs_ids) for _, rhs_ids in sorted(rs)]

    def enum_buckets(self):
        rhs_id_order = self.gen_rhs_order()
        for lN in range(1, self.maxL+1):
            lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
            for lhs_ids in multicomb(lhs_mc_ids, lN):
                assert all(id0<=id1 for id0,id1 in zip(lhs_ids[:-1],lhs_ids[1:]))
                for rhs_ids in rhs_id_order:
                    if self.custom_filter(lhs_ids, rhs_ids):
                        continue
                    yield (lhs_ids, rhs_ids)

    def num_combinations(self):
        return sum(1 for _ in self.enum_buckets())

    def gen_all_T2(self, lhs_ops, rhs_ops):
        def get_cnt(op, k):
            return {T:len(ids) for T, ids in comb_type_to_nT(op.get_type()[k]).items()}

        def count(l):
            ret = {}
            for d in l:
                for n, v in d.items():
                    ret[n] = ret.get(n, 0) + v
            return ret

        lhs_iTs = count([get_cnt(op, 0) for op in lhs_ops])
        lhs_oTs = count([get_cnt(op, 1) for op in lhs_ops])
        rhs_iTs = count([get_cnt(op, 0) for op in rhs_ops])
        rhs_oTs = count([get_cnt(op, 1) for op in rhs_ops])
        if len(lhs_oTs) > 1 or len(rhs_oTs) > 1:
            raise NotImplementedError()
        max_lhs_oT = {T:1 for T in lhs_oTs.keys()}
        max_lhs_iT = {T:(cnt-(lhs_oTs.get(T,0) - max_lhs_oT.get(T, 0))) for T,cnt in lhs_iTs.items()}
        max_rhs_oT = {T:1 for T in rhs_oTs.keys()}
        max_rhs_iT = {T:(cnt-(rhs_oTs.get(T,0) - max_rhs_oT.get(T, 0))) for T,cnt in rhs_iTs.items()}

        i_keys = set(max_lhs_iT.keys()) | set(max_rhs_iT.keys())
        o_keys = set(max_lhs_oT.keys()) | set(max_rhs_oT.keys())
        max_iT = {T: min(max_lhs_iT.get(T, 0), max_rhs_iT.get(T, 0)) for T in i_keys}
        max_oT = {T: min(max_lhs_oT.get(T, 0), max_rhs_oT.get(T, 0)) for T in o_keys}

        i_poss = {T:list(reversed(range(1,m+1))) for T,m in max_iT.items()}
        o_poss = {T:list(reversed(range(1,m+1))) for T,m in max_oT.items()}
        for ivs in it.product(*list(i_poss.values())):
            iT = []
            for T, v in zip(i_poss.keys(), ivs):
                iT += [T for _ in range(v)]
            for ovs in it.product(*list(o_poss.values())):
                oT = []
                for T, v in zip(o_poss.keys(), ovs):
                    oT += [T for _ in range(v)]
                assert len(oT) == 1
                yield (tuple(iT), tuple(oT))

    def gen_all_T1(self, ops):
        def get_cnt(op, k):
            return {T:len(ids) for T, ids in comb_type_to_nT(op.get_type()[k]).items()}

        def count(l):
            ret = {}
            for d in l:
                for n, v in d.items():
                    ret[n] = ret.get(n, 0) + v
            return ret

        iTs = count([get_cnt(op, 0) for op in ops])
        oTs = count([get_cnt(op, 1) for op in ops])
        if len(oTs) > 1:
            raise NotImplementedError()
        max_oT = {T:1 for T in oTs.keys()}
        max_iT = {T:(cnt-(oTs.get(T,0) - max_oT.get(T, 0))) for T,cnt in iTs.items()}


        #There is a partial order of input types. It forms a lattice.
        #I need to return a full group where each group is equal
        i_poss = {T:list(reversed(range(1,m+1))) for T,m in max_iT.items()}
        o_poss = {T:list(reversed(range(1,m+1))) for T,m in max_oT.items()}
        ivss = [(sum(ivs),ivs) for ivs in it.product(*list(i_poss.values()))]
        grouped_ivs = {}
        for (s, ivs) in ivss:
            grouped_ivs.setdefault(s,[]).append(ivs)
        for s, ivss in sorted(grouped_ivs.items()):
            print(s)
            group = []
            for ivs in ivss:
                iT = []
                for T, v in zip(i_poss.keys(), ivs):
                    iT += [T for _ in range(v)]
                for ovs in it.product(*list(o_poss.values())):
                    oT = []
                    for T, v in zip(o_poss.keys(), ovs):
                        oT += [T for _ in range(v)]
                    assert len(oT) == 1
                    group.append((tuple(iT), tuple(oT)))
            yield group

    # Finds all combinations of rules that exactly match the lhs and have less cost than or eq to the rhs
    def all_rule_covers(self, lhs_ids, rhs_ids, iT, oT):
        exp_cost = sum([self.costs[ri] for ri in rhs_ids])
        assert isinstance(exp_cost, int)
        iTs = _list_to_counts(iT)
        oTs = _list_to_counts(oT)
        lhs_op_cnt = _list_to_counts([self.lhss[lid].qualified_name for lid in lhs_ids])
        #Prefiltering
        poss_rules = {}
        for ri, (rule, ri_cost) in enumerate(zip(self.rdb.rules, self.rdb.costs)):
            if ri_cost > exp_cost:
                continue
            elif rule.lhs.op_cnt == lhs_op_cnt:
                rule_iTs = _list_to_counts(rule.lhs.iT)
                #if all(rule_iTs.get(T,0) >=cnt for T, cnt in iTs.items()):
                #    print("RCNT", {ri:1},flush=True)
                #    yield [(rule.lhs, 1)]
                yield [(rule.lhs, 1)]
            elif set(lhs_op_cnt.keys()) >= set(rule.lhs.op_cnt.keys()):
                if all([rule.lhs.op_cnt.get(op, 0) <= cnt for op, cnt in lhs_op_cnt.items()]):
                    #Check that typing works
                    poss_rules[ri] = (rule.lhs.op_cnt, (rule.lhs.iT, rule.lhs.oT), ri_cost)
        if len(poss_rules) == 0:
            return

        #Early out if there is not at least one matching op over all poss rules
        poss_ops = functools.reduce(lambda s0, s1: s0|s1, [set(op_cnt.keys()) for op_cnt,_,_ in poss_rules.values()])
        if poss_ops != set(lhs_op_cnt.keys()):
            return


        rvarT = ht.SMTBitVector[32]
        max_rvar = max(cnt for cnt in lhs_op_cnt.values())
        lhs_op_cnts = {op:rvarT(0) for op in lhs_op_cnt.keys()}
        cost = rvarT(0)
        rvars = {ri:get_var(f"R{ri}", 32) for ri in poss_rules.keys()}
        lhs_iTs = {}
        lhs_oTs = {}
        for ri, (op_cnt, (r_iT, r_oT), ri_cost) in poss_rules.items():
            rvar = rvars[ri]
            #Cost
            cost += rvar*ri_cost

            #op count is good
            for op, cnt in op_cnt.items():
                assert op in lhs_op_cnts
                lhs_op_cnts[op] += rvar*cnt

            #Typing is good
            for T, cnt in _list_to_counts(r_iT).items():
                v = lhs_iTs.get(T,rvarT(0))
                lhs_iTs[T] = v + rvar*cnt
            for T, cnt in _list_to_counts(r_oT).items():
                v = lhs_oTs.get(T,rvarT(0))
                lhs_oTs[T] = v + rvar*cnt

        #Using lhs_oTs is a bit of a hack. This is assuming that rules only have 1 output
        max_lhs_oT = lhs_oTs
        max_lhs_iT = {T:(cnt-(lhs_oTs.get(T,0) - max_lhs_oT.get(T, 0))) for T,cnt in lhs_iTs.items()}
        iT_conds = []
        for T, cnt in iTs.items():
            iT_conds.append(max_lhs_iT[T] >= cnt)
        lconds = []
        for op, cnt in lhs_op_cnts.items():
            lconds.append(cnt == lhs_op_cnt[op])
        max_rvars = [rvar <= max_rvar for rvar in rvars.values()]
        f = fc.And([
            fc.And(max_rvars),
            fc.And(lconds),
            #fc.And(iT_conds),
            cost <= exp_cost
        ])
        #TODO
        #print("DEBUG")
        #print(f.serialize())
        for sol in smt_solve_all(f.to_hwtypes().value):
            r_cnt = {}
            for ri, rvar in rvars.items():
                assert rvar.value in sol
                rval = _to_int(sol[rvar.value])
                if rval != 0:
                    r_cnt[ri] = rval
            print("RCNT", r_cnt,flush=True)
            lhs_pats = [(self.rdb.rules[ri].lhs, cnt) for ri, cnt in r_cnt.items()]
            yield lhs_pats


    def gen_all(self, opts=SolverOpts()):
        rhs_id_order = self.gen_rhs_order()
        for lN in range(1, self.maxL+1):
            lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
            for lhs_ids in multicomb(lhs_mc_ids, lN):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                for rhs_ids in rhs_id_order:
                    rhs_ops = [self.rhss[i] for i in rhs_ids]
                    for (iT, oT) in self.gen_all_T2(lhs_ops, rhs_ops):
                        if self.custom_filter(lhs_ids, rhs_ids):
                            continue
                        if opts.log:
                            print_kind(lhs_ids, rhs_ids)

                        #Discover all lhs pattern covers
                        if self.pgf:
                            covers = list(self.all_rule_covers(lhs_ids, rhs_ids, iT, oT))
                        else:
                            covers = []
                        if opts.log:
                            print_iot(iT, oT)
                        info = ((tuple(lhs_ids), tuple(rhs_ids)), (iT, oT))
                        rs = RuleSynth(
                            iT,
                            oT,
                            lhs_op_list=lhs_ops,
                            rhs_op_list=rhs_ops,
                            pat_en_t=self.pat_en_t,
                            sym_opts=self.sym_opts,
                        )
                        for cover in covers:
                            rs.add_rule_cover(cover)

                        for i, (sol, t) in enumerate(rs.cegis_all(opts)):
                            lhs_pat = rs.lhs_cs.pattern_from_sol(sol)
                            rhs_pat = rs.rhs_cs.pattern_from_sol(sol)
                            rule = Rule(i, lhs_pat, rhs_pat, t, info)
                            assert rule.verify()
                            rule_cost = sum([self.costs[self.rhs_name_to_id[op]]*cnt for op, cnt in rule.rhs.op_cnt.items()])
                            self.rdb.add_rule(rule, rule_cost)
                            yield rule
                            #Force the new cover to be used in the current it
                            #Recalculate the covers generator for other Types
                            if self.igf:
                                cur_cover = [(lhs_pat, 1)]
                                rs.add_rule_cover(cur_cover)
                                covers.append(cur_cover)