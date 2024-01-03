from comb.synth.pattern import Pattern, SymOpts, all_prog, onepat, IPerm
from comb.synth.instruction_sel import OptimalInstructionSel
import itertools as it
from .utils import flat
from comb.synth.solver_utils import SolverOpts

from comb.synth.verify import verify
import hwtypes.smt_utils as fc


class Rule:
    def __init__(self, lhs_pat: Pattern, rhs_pat: Pattern, id: int, synth_time: float, cost=0):
        self.id = id
        self.lhs: Pattern = lhs_pat
        self.rhs: Pattern = rhs_pat
        self.iT = lhs_pat.iT
        self.oT = lhs_pat.oT
        self.time = synth_time
        self.cost = cost
        #self.comm_info = get_comm_info(lhs_pat.to_comb(), opts)
        self.eq_rules = []
        self.NI = len(lhs_pat.iT)
        self.NO = len(lhs_pat.oT)

    def serialize(self, ns, i):
        lhs = self.lhs.to_comb(ns, f"L{i}").serialize()
        rhs = self.rhs.to_comb(ns, f"R{i}").serialize()
        return lhs + "\n\n" + rhs


    def verify(self):
        lcomb = self.lhs.to_comb()
        rcomb = self.rhs.to_comb()
        ce = verify(lcomb, rcomb)
        return ce is None

    #def update_time(self, ts):
    #    self.time.extend(ts)

    #def add_equiv(self, rule: 'Rule'):
    #    self.eq_rules.append(rule)

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
        NL = sum([len(x) for x in PL[3]])
        NR = sum([len(x) for x in PR[3]])
        for iperm in it.permutations(I):
            map = {i:j for i, j in enumerate(iperm)}
            mapL = {**map, **{i+NI:i+NI for i in range(NL)}}
            mapR = {**map, **{i+NI:i+NI for i in range(NR)}}
            yield IPerm(PL, mapL), IPerm(PR, mapR)


    def ruleL(self, l_pat_enc, r_pat_enc, lhs_op_mapping, rhs_op_mapping):
        #enums patterns
        l_enum = self.lhs.enum_CK()
        r_enum = self.rhs.enum_CK()
        allr = []
        for (l_edges, l_synth_vals),(r_edges, r_synth_vals) in it.product(l_enum, r_enum):
            l_pat = Pattern(self.lhs.iT, self.lhs.oT, self.lhs.ops, l_edges, l_synth_vals)
            r_pat = Pattern(self.rhs.iT, self.rhs.oT, self.rhs.ops, r_edges, r_synth_vals)
            l = l_pat_enc.match_one_pattern(l_pat, lhs_op_mapping)
            r = r_pat_enc.match_one_pattern(r_pat, rhs_op_mapping)
            allr.append(fc.And([l,r]))
        return fc.Or(allr).to_hwtypes()


import pickle

class RuleDatabase:
    def __init__(self, cost = None):
        self.cost = cost
        #self.rules = {} #[numIR][numISA][irids][isaids] = (rule)
        self.rules = {} #[(l_ids, r_ids, NI)] -> Rules
        self.time = {} #[(l_ids, r_ids, NI)] -> Rules
        #self.cover_times = {}
        #self.enum_time = 0
        #self.rcnt = 0

    #def add_enum_time(self, et):
    #    self.enum_time += et

    #def add_cover_time(self, k, t):
    #    n = len(self)
    #    self.cover_times[k] = (t, n)

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
        info = {}
        for k, (st, ct, et) in self.time.items():
            new_rules = self.rules[k]
            extra = len(st) - len(new_rules)
            sat_time = round(sum(st),3)
            extra_time = round(ct+et,3)
            assert extra >=0
            info[k] = dict(
                u=len(new_rules),
                e=extra,
                st=sat_time,
                et=extra_time,
            )
        return info
        #return dict(
        #    times=[(len(r.time), sum(r.time)) for r in self.enum_rules()],
        #    #covers=self.cover_times,
        #    #enum=self.enum_time,
        #)

    @property
    def mn_info(self):
        mn_cnt = {}
        for (lids, rids, NI), info in self.time_info.items():
            mn = (len(lids),len(rids))
            mn_cnt[mn] = mn_cnt.get(mn, 0) + info['u']
        return mn_cnt

    def pickle_info(self, file):
        v = dict(
            t=self.time_info,
            mn=self.mn_info,
        )
        with open(file, 'wb') as f:
            pickle.dump(v, f, protocol=pickle.HIGHEST_PROTOCOL)

    def add_rules(self, key, rules, times):
        assert key not in self.rules
        self.rules[key] = rules
        self.time[key] = times

    def enum_rules(self):
        for k, rules in self.rules.items():
            for i, rule in enumerate(rules):
                yield (k, i, rule)

    @property
    def num_rules(self):
        return sum(len(rs) for rs in self.rules.values())

    def find_all_composites(self):
        rules_all = flat(self.rules.values())

        solverops = SolverOpts(solver_name='z3')
        symops = SymOpts(True, True, False)
        composites = []

        for i,rule in enumerate(rules_all):
            if i == 60:
                pass
            components = rules_all[:i] + rules_all[i+1:]
            instr_sel = OptimalInstructionSel(rule.lhs, components, symops, solverops)
            if instr_sel.run(rule.cost):
                composites.append(i)
        return composites 



    #This only works for non-lowcost
    #def add_rule(self, rule: Rule):
    #    rule.id = self.rcnt
    #    self.rcnt += 1
    #    lN = len(rule.lhs.ops)
    #    rN = len(rule.rhs.ops)
    #    lcnt = str(sorted(rule.lhs.op_cnt.items()))
    #    rcnt = str(sorted(rule.rhs.op_cnt.items()))
    #    rules = self.get(lN, rN, lcnt, rcnt)
    #    assert isinstance(rules, list)
    #    new_rule = True
    #    for erule in rules:
    #        eq = erule.equal(rule)
    #        if eq:
    #            assert rule.equal(erule)
    #            print("EQUAL RULE", flush=True)
    #            #print("NEW")
    #            #print(rule)
    #            #print("="*100)
    #            #print("OLD")
    #            #print(erule)
    #            #print("END EQUAL RULE")
    #            new_rule = False
    #            erule.update_time(rule.time)
    #            erule.add_equiv(rule)
    #            break
    #    if new_rule:
    #        print("NEW RULE", rule.id, flush=True)
    #        rules.append(rule)

    def __len__(self):
        return len(self.enum_rules())

    #def p(self):
    #    for ri, rule in enumerate(self.enum_rules()):
    #        print("RULE", ri)
    #        print(rule)
    #        print("ENDRULE")

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


    #def get(self, *keys):
    #    rules = self.rules
    #    for k, d in zip(keys, [{} for _ in keys[:-1]] + [[]]):
    #        rules.setdefault(k, d)
    #        rules = rules[k]
    #    return rules

    #def enum_rules(self):
    #    for r1 in self.rules.values():
    #        for r2 in r1.values():
    #            for r3 in r2.values():
    #                for r4 in r3.values():
    #                    for r in r4:
    #                        yield r

    #def get_m2n(self):
    #    m2n = {}
    #    for m, r2 in self.rules.items():
    #        for n, r3 in r2.items():
    #            cnt = 0
    #            for r4 in r3.values():
    #                for r5 in r4.values():
    #                    assert isinstance(r5, list)
    #                    cnt += len(r5)
    #            m2n[(m,n)] = cnt
    #    return m2n
