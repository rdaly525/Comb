from comb.frontend.compiler import compile_program
from comb.synth.comm_synth import get_comm_info
from comb.synth.pattern import Pattern, SymOpts
import typing as tp
import itertools as it

from comb.synth.solver_utils import SolverOpts
from comb.synth.verify import verify
import hwtypes.smt_utils as fc


def IPerm(P, map):
    O = map[P[1]]
    IK = [[map[IKij] for IKij in IKi] for IKi in P[2]]
    return P[0], O, IK, P[3]

class Rule:
    def __init__(self, id:int, lhs_pat: Pattern, rhs_pat: Pattern, synth_time: float, opts: SolverOpts= SolverOpts()):
        self.id = id
        self.lhs: Pattern = lhs_pat
        self.rhs: Pattern = rhs_pat
        self.iT = lhs_pat.iT
        self.oT = lhs_pat.oT
        self.time = [synth_time]
        self.comm_info = get_comm_info(lhs_pat.to_comb(), opts)
        self.eq_rules = []

    def serialize(self, ns, i):
        lhs = self.lhs.to_comb(ns, f"L{i}").serialize()
        rhs = self.rhs.to_comb(ns, f"R{i}").serialize()
        return lhs + "\n\n" + rhs


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

    def enum_input_perm(self, PL, PR):
        I = PL[0]
        NI = len(I)
        NL = len(PL[3])
        NR = len(PR[3])
        for iperm in it.permutations(I):
            map = {i:j for i, j in enumerate(iperm)}
            mapL = {**map, **{i+NI:i+NI for i in range(NL)}}
            mapR = {**map, **{i+NI:i+NI for i in range(NR)}}
            yield IPerm(PL, mapL), IPerm(PR, mapR)


    def ruleL(self, L_IR, L_ISA):
        l_enum = self.lhs.enum_all_equal(en_I=False)
        r_enum = self.rhs.enum_all_equal(en_I=False)
        allr = []
        for rule in it.product(l_enum, r_enum):
            for PL, PR in self.enum_input_perm(*rule):
                l = onepat(PL, L_IR)
                r = onepat(PR, L_ISA)
                allr.append(l & r)
        return fc.Or(allr).to_hwtypes()

def onepat(P, L):
    #Output
    cond = [P[1]==L[1]]

    #K ins
    cond.append(fc.And([fc.And([Pij==Lij for Pij, Lij in zip(Pi, Li)]) for Pi, Li in zip(P[2], L[2])]))

    #K outs
    cond.append(fc.And([Pi==Li for Pi, Li in zip(P[3], L[3])]))
    return fc.And(cond).to_hwtypes()

import pickle

class RuleDatabase:
    def __init__(self, cost = None):
        self.cost = cost
        self.rules = {} #[numIR][numISA][irids][isaids] = (rule)
        self.cover_times = {}
        self.enum_time = 0
        self.rcnt = 0

    def add_enum_time(self, et):
        self.enum_time += et

    def add_cover_time(self, k, t):
        n = len(self)
        self.cover_times[k] = (t, n)

    #def get(self, r: Rule):
    #    for r_ in self.rules:
    #        if r.equal(r_):
    #            assert r_.equal(r)
    #            return r_
    #    return None

    def save(self, ns, file):
        with open(file, 'w') as f:
            for ri, rule in enumerate(self.rules):
                f.write(rule.serialize(ns, ri) + "\n\n\n")

    #def load(self, ns, file):
    #    assert len(self.rules)==0
    #    with open(file, 'r') as f:
    #        obj = compile_program(f.read())
    #    for ri in it.count(1):
    #        lhs_comb = obj.get(ns, f"L{ri}")
    #        rhs_comb = obj.get(ns, f"R{ri}")
    #        self.add_rule(
    #            Rule(
    #                ri,
    #                Pattern.from_comb(lhs_comb),
    #                Pattern.from_comb(rhs_comb),
    #                0,
    #            ),
    #            0
    #        )

    @property
    def time_info(self):
        return dict(
            times=[(len(r.time), sum(r.time)) for r in self.enum_rules()],
            covers=self.cover_times,
            enum=self.enum_time,
        )


    def pickle_time(self, file):
        v = self.time_info
        with open(file, 'wb') as f:
            pickle.dump(v, f, protocol=pickle.HIGHEST_PROTOCOL)

    def get(self, *keys):
        rules = self.rules
        for k, d in zip(keys, [{} for _ in keys[:-1]] + [[]]):
            rules.setdefault(k, d)
            rules = rules[k]
        return rules

    def enum_rules(self):
        for r1 in self.rules.values():
            for r2 in r1.values():
                for r3 in r2.values():
                    for r4 in r3.values():
                        for r in r4:
                            yield r

    def get_m2n(self):
        m2n = {}
        for m, r2 in self.rules.items():
            for n, r3 in r2.items():
                cnt = 0
                for r4 in r3.values():
                    for r5 in r4.values():
                        assert isinstance(r5, list)
                        cnt += len(r5)
                m2n[(m,n)] = cnt
        return m2n

    def add_rule(self, rule: Rule, cost: int, filter=True):
        rule.id = self.rcnt
        self.rcnt += 1
        lN = len(rule.lhs.ops)
        rN = len(rule.rhs.ops)
        lcnt = str(sorted(rule.lhs.op_cnt.items()))
        rcnt = str(sorted(rule.rhs.op_cnt.items()))
        rules = self.get(lN, rN, lcnt, rcnt)
        assert isinstance(rules, list)
        new_rule = True
        for erule in rules:
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
                erule.update_time(rule.time)
                erule.add_equiv(rule)
                break
        if new_rule:
            print("NEW RULE", rule.id, flush=True)
            rules.append(rule)

    def __len__(self):
        return len(self.enum_rules())

    def p(self):
        for ri, rule in enumerate(self.enum_rules()):
            print("RULE", ri)
            print(rule)
            print("ENDRULE")

    #def post_filter(self):
    #    #TODO This does not take into generalized rules
    #    prims = []
    #    for ri, r in enumerate(self.rules):
    #        prim = True
    #        for pi, p in enumerate(prims):
    #            eq = r.equal(p)
    #            if eq:
    #                assert r.equal(p)
    #                print("EQUAL RULE")
    #                print(r)
    #                print("="*30)
    #                print(p)
    #                print("END EQUAL RULE")
    #                prim = False
    #                p.update_time(r.time)
    #                break
    #            else:
    #                assert not p.equal(r)
    #        if prim:
    #            prims.append(r)
    #    self.rules = prims

    #def sort(self, maxL, maxR):
    #    table = {l+1:{r+1:[0,0] for r in range(maxR)} for l in range(maxL)}
    #    for rule in self.rules:
    #        num_filter = len(rule.time)
    #        #lids, rids = rule.info[0]
    #        nL = len(lids)
    #        nR = len(rids)
    #        pre,post = table[nL][nR]
    #        table[nL][nR] = (pre+num_filter,post+1)
    #    return table

    #def diff(self, other: 'RuleDatabase'):
    #    ldb, rdb = self, other
    #    for lri, lr in enumerate(ldb.rules):
    #        for rri, rr in enumerate(rdb.rules):
    #            if lr.equal(rr):
    #                print(f"L,R = {lri},{rri}")

