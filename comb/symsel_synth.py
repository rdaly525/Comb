from comb import Comb
from comb.ast import QSym, TypeCall, BVType, IntValue
from comb.double_synth import Strat2Synth
from comb.synth import Cegis, CombSynth, SolverOpts, flat, smt_solve_all, _to_int
import hwtypes.smt_utils as fc
import hwtypes as ht
import typing as tp
import itertools as it
from dataclasses import dataclass
#This is the motherload of classes
#It is the discovery engine that leverages the symbolic instruction selection
from more_itertools import distinct_combinations as multicomb


def smart_iter(mL: int, mR: int):
    for s in range(2, mL+mR+1):
        for l in range(1, s):
            r = s-l
            if l <= mL and r <= mR:
                yield (l, r)

def _list_to_counts(vals):
    ret = {}
    for v in vals:
        ret[v] = ret.get(v, 0) + 1
    return ret

@dataclass
class Rule:
    lhs_comb: Comb
    rhs_comb: Comb
    lhs_ids: tp.List[int]
    rhs_ids: tp.List[int]
    def __post_init__(self):
        self.lhs_cnt = _list_to_counts(self.lhs_ids)
        self.rhs_cnt = _list_to_counts(self.rhs_ids)

    def __str__(self):
        ret = str(self.lhs_comb)
        ret += "\n ----->\n"
        ret += str(self.rhs_comb)
        return ret

@dataclass
class SymSelSynth:
    lhss: tp.Set[Comb]
    rhss: tp.Set[Comb]
    maxL: int
    maxR: int
    T: object = ht.SMTBitVector[16]

    def __post_init__(self):
        self.lhss = list(self.lhss)
        self.rhss = list(self.rhss)
        self.rules: tp.List[Rule] = []
        self.rule_vars = []
        #Create integer variables for each kind
        pass

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
                lhs_op_cnts[li] += cnt*rvar
            rhs_cnts = self.rules[i].rhs_cnt
            for ri, cnt in rhs_cnts.items():
                rhs_op_cnts[ri] += cnt*rvar
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
                exp_cnt = exp_lhs_cnt[ri]
            rconds.append(cnt == exp_cnt)
        max_rvars = [rvar <5 for rvar in self.rule_vars]
        f = fc.And([fc.And(lconds), fc.And(rconds), fc.And(max_rvars)])
        print("DEBUG")
        print(f.serialize())
        for sol in smt_solve_all(f.to_hwtypes().value):
            r_cnt = {}
            for ri, rvar in self.rule_vars:
                assert rvar.value in sol
                rval = _to_int(sol[rvar.value])
                if rval != 0:
                    r_cnt[ri] = rval
            yield r_cnt


    #TODO this should be a more intelligent enumeration in terms of the typing of each op
    def gen_all_T(self, lhs_ops, rhs_ops):
        BVN = TypeCall(BVType(), [IntValue(3)])
        for iN in reversed(range(1, 4)):
            iT = [BVN for _ in range(iN)]
            oT = [BVN for _ in range(1)]
            yield (iT, oT)

    def gen_all(self, opts=SolverOpts()):
        for lN, rN, in smart_iter(self.maxL, self.maxR):
            lhs_mc_ids = flat([[i for _ in range(lN)] for i in range(len(self.lhss))])
            rhs_mc_ids = flat([[i for _ in range(rN)] for i in range(len(self.rhss))])
            for (lhs_ids, rhs_ids) in it.product(multicomb(lhs_mc_ids, lN), multicomb(rhs_mc_ids, rN)):
                lhs_ops = [self.lhss[i] for i in lhs_ids]
                rhs_ops = [self.rhss[i] for i in rhs_ids]
                print("*"*80)
                op_strs = ["[" + ", ".join(str(op.name) for op in ops) + "]" for ops in (lhs_ops, rhs_ops)]
                print(f"{op_strs[0]} -> {op_strs[1]}")

                covers = self.all_rule_covers(lhs_ids, rhs_ids)

                for (iT, oT) in self.gen_all_T(lhs_ops, rhs_ops):
                    #How to determine the Input/Output Types??
                    ss = Strat2Synth(
                        comb_type=(iT, oT),
                        lhs_op_list=lhs_ops,
                        rhs_op_list=rhs_ops,
                    )
                    for cover in covers:
                        rules = [self.rules[ci] for ci in cover]
                        ss.add_rule_cover(rules)
                for (lhs_comb, rhs_comb) in ss.gen_all_sols(opts=opts):
                    rule = Rule(lhs_comb, rhs_comb, lhs_ids, rhs_ids)
                    self.add_rule(rule)
                    yield rule