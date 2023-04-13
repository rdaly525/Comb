from comb import Comb
from comb.frontend.ast import TypeCall, BVType, IntValue
from comb.synth.pattern import PatternEncoding, SymOpts
from comb.synth.rule import Rule
from comb.synth.rule_synth import RuleSynth
from comb.synth.solver_utils import SolverOpts, smt_solve_all
from comb.synth.utils import _list_to_counts, flat, _to_int, comb_type_to_nT

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
    maxL: int
    maxR: int
    pat_en_t: tp.Type[PatternEncoding]
    sym_opts: SymOpts
    opMaxL: tp.Mapping[int, int] = None
    opMaxR: tp.Mapping[int, int] = None

    def __post_init__(self):
        if self.opMaxL is None:
            self.opMaxL = {i:self.maxL for i in range(len(self.lhss))}
        if self.opMaxR is None:
            self.opMaxR = {i:self.maxR for i in range(len(self.rhss))}
        self.lhss = list(self.lhss)
        self.rhss = list(self.rhss)
        self.rules: tp.List[Rule] = []


    def gen_all(self, opts=SolverOpts()):
        raise NotImplementedError()


    def num_ss_calls(self):
        for lN, rN, in smart_iter(self.maxL, self.maxR):
            lhs_mc_ids = flat([[i for _ in range(lN)] for i in range(len(self.lhss))])
            rhs_mc_ids = flat([[i for _ in range(rN)] for i in range(len(self.rhss))])
            for (lhs_ids, rhs_ids) in it.product(multicomb(lhs_mc_ids, lN), multicomb(rhs_mc_ids, rN)):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                rhs_ops = [self.rhss[i] for i in rhs_ids]
                if custom_filter(rhs_ids):
                    continue
                for (iT, oT) in self.gen_all_T(lhs_ops, rhs_ops):
                    yield None

    def gen_all_T(self, lhs_ops, rhs_ops):
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


def custom_filter(ids):
    if ids == [0,0,2]:
        return True
    if 2 in ids and 3 in ids:
        return True

class RulePostFilter(RuleDiscovery):

    def gen_all(self, opts=SolverOpts()):
        #print("TOT:", sum(1 for _ in self.num_ss_calls()))
        for lN, rN, in smart_iter(self.maxL, self.maxR):
            #lhs_mc_ids = flat([[i for _ in range(lN)] for i in range(len(self.lhss))])
            #rhs_mc_ids = flat([[i for _ in range(rN)] for i in range(len(self.rhss))])
            lhs_mc_ids = flat([[i for _ in range(self.opMaxL[i])] for i in range(len(self.lhss))])
            rhs_mc_ids = flat([[i for _ in range(self.opMaxR[i])] for i in range(len(self.rhss))])
            for (lhs_ids, rhs_ids) in it.product(multicomb(lhs_mc_ids, lN), multicomb(rhs_mc_ids, rN)):
                assert all(id0<=id1 for id0,id1 in zip(rhs_ids[:-1],rhs_ids[1:]))
                if custom_filter(rhs_ids):
                    continue
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                rhs_ops = [self.rhss[i] for i in rhs_ids]
                #print("*"*80)
                #op_strs = ["(" + ", ".join(str(op.qualified_name) for op in ops) + ")" for ops in (lhs_ops, rhs_ops)]
                if opts.log:
                    print_kind(lhs_ids, rhs_ids)
                for (iT, oT) in self.gen_all_T(lhs_ops, rhs_ops):
                    if opts.log:
                        print_iot(iT, oT)
                    info = ((tuple(lhs_ids), tuple(rhs_ids)), (iT, oT))
                    ss = RuleSynth(
                        iT,
                        oT,
                        lhs_op_list=lhs_ops,
                        rhs_op_list=rhs_ops,
                        pat_en_t=self.pat_en_t,
                        sym_opts=self.sym_opts,
                    )
                    for i, (sol, t) in enumerate(ss.cegis_all(opts)):
                        lhs_pat = ss.lhs_cs.pattern_from_sol(sol)
                        rhs_pat = ss.rhs_cs.pattern_from_sol(sol)
                        rule = Rule(lhs_pat, rhs_pat, t, info)
                        self.rules.append(rule)
                        yield rule


class RulePreFilter(RuleDiscovery):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.rule_vars: tp.List[Rule] = []

    def add_rule(self, rule: Rule):
        var = self.T(prefix=f"Rule{len(self.rules)}")
        self.rule_vars.append(var)
        self.rules.append(rule)

    #Sets up a solve #Find a multiset of rules
    def all_rule_covers(self, lhs_ids, rhs_ids):
        exp_lhs_cnt = _list_to_counts(lhs_ids)
        exp_rhs_cnt = _list_to_counts(rhs_ids)
        lhs_op_cnts = [self.T(0) for _ in self.lhss]
        rhs_op_cnts = [self.T(0) for _ in self.rhss]
        for i, rvar in enumerate(self.rule_vars):
            lhs_cnts = self.rules[i].lhs_cnt
            for li, cnt in lhs_cnts.items():
                lhs_op_cnts[li] += rvar*cnt
            rhs_cnts = self.rules[i].rhs_cnt
            for ri, cnt in rhs_cnts.items():
                rhs_op_cnts[ri] += rvar*cnt
        lconds = []
        for li, cnt in enumerate(lhs_op_cnts):
            exp_cnt = 0
            if li in exp_lhs_cnt:
                exp_cnt = exp_lhs_cnt[li]
            lconds.append(cnt == exp_cnt)

        rconds = []
        for ri, cnt in enumerate(rhs_op_cnts):
            exp_cnt = 0
            if ri in exp_rhs_cnt:
                exp_cnt = exp_rhs_cnt[ri]
            rconds.append(cnt == exp_cnt)
        max_rvars = [rvar <5 for rvar in self.rule_vars]
        f = fc.And([fc.And(lconds), fc.And(rconds), fc.And(max_rvars)])
        #print("DEBUG")
        #print(f.serialize())
        for sol in smt_solve_all(f.to_hwtypes().value):
            r_cnt = {}
            for ri, rvar in enumerate(self.rule_vars):
                assert rvar.value in sol
                rval = _to_int(sol[rvar.value])
                if rval != 0:
                    r_cnt[ri] = rval
            print("RCNT", r_cnt)
            rules = [(self.rules[ci], cnt) for ci, cnt in r_cnt.items()]
            yield rules


    def gen_all(self, opts=SolverOpts()):
        print("TOT:", sum(1 for _ in self.num_ss_calls()))
        for lN, rN, in smart_iter(self.maxL, self.maxR):
            lhs_mc_ids = flat([[i for _ in range(lN)] for i in range(len(self.lhss))])
            rhs_mc_ids = flat([[i for _ in range(rN)] for i in range(len(self.rhss))])
            for (lhs_ids, rhs_ids) in it.product(multicomb(lhs_mc_ids, lN), multicomb(rhs_mc_ids, rN)):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                rhs_ops = [self.rhss[i] for i in rhs_ids]
                print("*"*80)
                op_strs = ["(" + ", ".join(str(op.qualified_name) for op in ops) + ")" for ops in (lhs_ops, rhs_ops)]
                print(f"{op_strs[0]} -> {op_strs[1]}")

                covers = list(self.all_rule_covers(lhs_ids, rhs_ids))

                for (iT, oT) in self.gen_all_T(lhs_ops, rhs_ops):
                    print("iT:", tuple(str(t) for t in iT))
                    #How to determine the Input/Output Types??
                    ss = RuleSynth(
                        comb_type=(iT, oT),
                        lhs_op_list=lhs_ops,
                        rhs_op_list=rhs_ops,
                    )
                    for cover in covers:
                        ss.add_rule_cover(cover)
                    for i in it.count(start=1):
                        sol = ss.cegis(opts)
                        if sol is None:
                            break
                        #lhs_comb = ss.lhs_cs.comb_from_solved(sol, name=QSym('solved', f"lhs_v{i}"))
                        #rhs_comb = ss.rhs_cs.comb_from_solved(sol, name=QSym('solved', f"rhs_v{i}"))
                        lhs_pat = ss.lhs_cs.pattern_from_solved(sol)
                        rhs_pat = ss.rhs_cs.pattern_from_solved(sol)
                        rule = Rule(lhs_pat, rhs_pat, lhs_ids, rhs_ids)
                        self.add_rule(rule)
                        yield rule
                        #Force the new cover to be used in the current it
                        #Recalculate the covers generator for other Types
                        cur_cover = [(rule, 1)]
                        ss.add_rule_cover(cur_cover)
                        covers.append(cur_cover)
