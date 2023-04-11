from comb.synth.pattern import Pattern, SymOpts
import typing as tp

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
        l_perm = lp0.equal_with_perm(lp1, opts)
        if l_perm is None:
            return False
        rp0 = self.rhss[0]
        rp1 = other.rhss[0]
        r_perm = rp0.equal_with_perm(rp1, opts)
        if r_perm is None:
            return False
        if l_perm == r_perm:
            return True
        return False




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
        prim_rules = []
        for ri, rule in enumerate(self.rules):
            prim = True
            for pi, other in enumerate(prim_rules):
                eq = rule.equal(other)
                if eq:
                    if not other.equal(rule):
                        eq0 = rule.equal(other)
                        eq1 = other.equal(rule)
                        print(eq0, eq1)
                        assert eq1

                    assert other.equal(rule)
                    prim = False
                    break
                else:
                    if other.equal(rule):
                        eq0 = rule.equal(other)
                        eq1 = other.equal(rule)
                        print(eq0, eq1)
                        assert not eq1
                    assert not other.equal(rule)
            if prim:
                prim_rules.append(rule)
        self.rules = prim_rules

    def diff(self, other: 'RuleDatabase'):
        ldb, rdb = self, other
        for lri, lr in enumerate(ldb.rules):
            for rri, rr in enumerate(rdb.rules):
                if lr.equal(rr):
                    print(f"L,R = {lri},{rri}")




