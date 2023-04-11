from comb.synth.pattern import Pattern, SymOpts
import typing as tp
import itertools as it

class Rule:
    def __init__(self, lhs_pat: Pattern, rhs_pat: Pattern):
        self.lhss: tp.List[Pattern] = [lhs_pat]
        self.rhss: tp.List[Pattern] = [rhs_pat]
        self.iT = lhs_pat.iT
        self.oT = lhs_pat.oT

    def __str__(self):
        ret = str(self.lhss[0].to_comb('R','R'))
        ret += "\n ----->\n"
        ret += str(self.rhss[0].to_comb('R','R'))
        return ret

    def equal(self, other: 'Rule'):
        opts = SymOpts(comm=True, same_op=True)
        #For now only do equality on 0
        lp0 = self.lhss[0]
        lp1 = other.lhss[0]
        l_matches = lp0.equal_with_match(lp1, opts)
        if len(l_matches)==0:
            return False
        rp0 = self.rhss[0]
        rp1 = other.rhss[0]
        r_matches = rp0.equal_with_match(rp1, opts)
        if len(r_matches)==0:
            return False
        return any(lm==rm for lm, rm in it.product(l_matches,r_matches))



class RuleDatabase:
    def __init__(self):
        self.rules: tp.List[Rule] = []

    def add_rule(self, rule: Rule):
        self.rules.append(rule)

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
                    prim = False
                    break
            if prim:
                prims.append(r)
        self.rules = prims

    def diff(self, other: 'RuleDatabase'):
        ldb, rdb = self, other
        for lri, lr in enumerate(ldb.rules):
            for rri, rr in enumerate(rdb.rules):
                if lr.equal(rr):
                    print(f"L,R = {lri},{rri}")




