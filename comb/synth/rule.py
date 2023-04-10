from comb.synth.pattern import Pattern

class Rule:
    def __init__(self, lhs_pat: Pattern, rhs_pat: Pattern):
        self.lhss = [lhs_pat]
        self.rhss = [rhs_pat]
        self.iT = lhs_pat.iT
        self.oT = lhs_pat.oT

    def __str__(self):
        ret = str(self.lhss[0])
        ret += "\n ----->\n"
        ret += str(self.rhss[0])
        return ret