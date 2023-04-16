from comb.synth.comm_synth import get_comm_info
from comb.synth.pattern import Pattern, SymOpts
import typing as tp
import itertools as it

from comb.synth.solver_utils import SolverOpts
from comb.synth.verify import verify


class Rule:
    def __init__(self, id:int, lhs_pat: Pattern, rhs_pat: Pattern, synth_time: float, info, opts: SolverOpts= SolverOpts()):
        self.id = id
        self.lhs: Pattern = lhs_pat
        self.rhs: Pattern = rhs_pat
        self.iT = lhs_pat.iT
        self.oT = lhs_pat.oT
        self.time = [synth_time]
        self.info = info
        self.comm_info = get_comm_info(lhs_pat.to_comb(), opts)
        self.eq_rules = []

    def verify(self):
        lcomb = self.lhs.to_comb()
        rcomb = self.rhs.to_comb()
        ce = verify(lcomb, rcomb)
        return ce is None

    def update_time(self, ts):
        self.time.extend(ts)

    def add_equiv(self, rule: 'Rule'):
        self.eq_rules.append(rule)

    @property
    def tot_time(self):
        return round(sum(self.time),2)

    def __str__(self):
        ret = str(self.lhs.to_comb(name=f"LHS{self.id}"))
        ret += "\n ----->\n"
        ret += str(self.rhs.to_comb(name=f"RHS{self.id}"))
        return ret

    def equal(self, other: 'Rule'):
        opts = SymOpts(comm=True, same_op=True)
        #For now only do equality on 0
        lp0 = self.lhs
        lp1 = other.lhs
        l_matches = lp0.equal_with_match(lp1, opts)
        if len(l_matches)==0:
            return False
        rp0 = self.rhs
        rp1 = other.rhs
        r_matches = rp0.equal_with_match(rp1, opts)
        if len(r_matches)==0:
            return False
        return any(lm==rm for lm, rm in it.product(l_matches,r_matches))


class RuleDatabase:
    def __init__(self):
        self.rules: tp.List[Rule] = []
        self.costs: tp.List[int] = []

    def add_rule(self, rule: Rule, cost: int, filter=True):
        i = len(self.rules)
        rule.id = i
        new_rule = True
        for erule in self.rules:
            eq = erule.equal(rule)
            if eq:
                assert rule.equal(erule)
                print("EQUAL RULE")
                print(erule)
                print("="*10, "New Rule")
                print(rule)
                print("-"*10, "New Rule")
                print(erule.lhs)
                print(rule.lhs)
                print("END EQUAL RULE")
                new_rule = False
                erule.update_time(rule.time)
                erule.add_equiv(rule)
                break
        if new_rule:
            self.rules.append(rule)
            self.costs.append(cost)

    def __len__(self):
        return len(self.rules)

    def p(self):
        for ri, rule in enumerate(self.rules):
            print("RULE", ri)
            print(rule)
            print("ENDRULE")

    def post_filter(self):
        #TODO This does not take into generalized rules
        prims = []
        for ri, r in enumerate(self.rules):
            prim = True
            for pi, p in enumerate(prims):
                eq = r.equal(p)
                if eq:
                    assert r.equal(p)
                    print("EQUAL RULE")
                    print(r)
                    print("="*30)
                    print(p)
                    print("END EQUAL RULE")
                    prim = False
                    p.update_time(r.time)
                    break
                else:
                    assert not p.equal(r)
            if prim:
                prims.append(r)
        self.rules = prims

    def sort(self, maxL, maxR):
        table = {l+1:{r+1:[0,0] for r in range(maxR)} for l in range(maxL)}
        for rule in self.rules:
            num_filter = len(rule.time)
            lids, rids = rule.info[0]
            nL = len(lids)
            nR = len(rids)
            pre,post = table[nL][nR]
            table[nL][nR] = (pre+num_filter,post+1)
        return table




    def diff(self, other: 'RuleDatabase'):
        ldb, rdb = self, other
        for lri, lr in enumerate(ldb.rules):
            for rri, rr in enumerate(rdb.rules):
                if lr.equal(rr):
                    print(f"L,R = {lri},{rri}")




