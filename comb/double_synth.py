from . import Comb
from .ast import QSym
from .synth import Cegis, CombSynth, SolverOpts, Pattern
from .utils import _list_to_dict, bucket_combinations, flat, comb_type_to_sT

import hwtypes.smt_utils as fc
import typing as tp
import itertools as it

#Stat2 is the following:
# Given:
#   N LHS instructions,
#   M RHS instructions,
#   A Type Signature (Inputs and outputs)
#       Really this is an input multiset and output multiset of Basic types
# Synthesize two programs that are equal to each other with the correct type signature
#
# Original Query
#  Exists(L1) Forall(V1) P1_wfp(L1) & (P1_lib & P1_conn) => P1_spec
#  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)


#Within a single pattern, match all the patterns
#Yields a map from pattern index to CombSynth index
def enum_pattern_partitions(p: Pattern, partitions):
    #Pattern: [A, A, B, C, C, C]
    #          0  1  2  3  4  5
    #Have:
    # A: [a0, a1], B: [b0], C: [c0, c1, c2]
    # Want:
    # [
    #   0: a0, 1: a1, 2: b0, 3: b0
    #
    #I need another level of enumeration
    #I currently have a set of matching ops. Now i need to assign each of those ops to each pattern idx
    if set(p.op_dict.keys()) != set(partitions.keys()):
        raise ValueError()
    assert set(p.op_dict.keys()) == set(partitions.keys())
    product_ids = []
    for op, p_ids in p.op_dict.items():
        cs_ids = partitions[op]
        assert len(p_ids) == len(cs_ids)
        product_ids.append(it.permutations(cs_ids))
    for op_perms in it.product(*product_ids):
        pid_to_csid = {}
        for cs_ids, (op, p_ids) in zip(op_perms, p.op_dict.items()):
            pid_to_csid = {**pid_to_csid, **{p_id:cs_id for p_id, cs_id in zip(p_ids, cs_ids)}}
        yield pid_to_csid


def enum_rule_partitions(op_list, rule_op_cnts):
    self_op_ids = _list_to_dict(op_list)
    op_to_rcnt = {op:{} for op in self_op_ids.keys()}
    for ri, op_cnt in enumerate(rule_op_cnts):
        for op in self_op_ids.keys():
            cnt = 0
            if op in op_cnt:
                cnt = op_cnt[op]
            op_to_rcnt[op][ri] = cnt

    #Verify sum of all ops in each rule adds up to total

    product_list = []
    for op, ids in self_op_ids.items():
        exp_cnt = len(ids)
        rcnt = sum(op_to_rcnt[op].values())
        assert exp_cnt == rcnt
        product_list.append(bucket_combinations(ids, list(op_to_rcnt[op].values())))
    for op_ids in it.product(*product_list):
        yield {op:ids for op, ids in zip(self_op_ids.keys(), op_ids)}


def match_one_pattern(p: Pattern, cs: CombSynth, pid_to_csid: tp.Mapping[int, int]):
    #Interior edges
    interior_edges = []
    for (li, lai), (ri, rai) in p.interior_edges:
        l_lvar = cs.op_out_lvars[pid_to_csid[li]][lai]
        r_csid = pid_to_csid[ri]
        r_lvars = cs.op_in_lvars[r_csid]
        r_lvar = r_lvars[rai]
        interior_edges.append(l_lvar==r_lvar)
    #Exterior edges
    in_lvars = {}
    for (li, lai), (ri, rai) in p.in_edges:
        assert li == "In"
        assert ri != "Out"
        r_lvar = cs.op_in_lvars[pid_to_csid[ri]][rai]
        in_lvars[lai] = r_lvar
    out_lvars = {}
    for (li, lai), (ri, rai) in p.out_edges:
        assert ri == "Out"
        assert li != "In"
        l_lvar = cs.op_out_lvars[pid_to_csid[li]][lai]
        out_lvars[lai] = l_lvar
    return fc.And(interior_edges), in_lvars, out_lvars


def match_pattern(p: Pattern, cs: CombSynth, ri_op_cnts):
    for pid_to_csid in enum_pattern_partitions(p, ri_op_cnts):
        yield match_one_pattern(p, cs, pid_to_csid)

def enum_dags(goal_T, rules):
    from .symsel_synth import Rule
    rules: tp.List[Rule] = rules
    goal_iT = comb_type_to_sT(goal_T[0])
    goal_oT = comb_type_to_sT(goal_T[1])
    rule_iTs = [comb_type_to_sT(r.comb_type[0]) for r in rules]
    rule_oTs = [comb_type_to_sT(r.comb_type[1]) for r in rules]

    if len(goal_iT) != 1:
        raise NotImplementedError()

    #Create a set of all sources/snks sorted by type
    srcs = {n:[("In", i) for i in ids] for n, ids in goal_iT.items()}
    for ri, rule_oT in enumerate(rule_oTs):
        for n, ids in rule_oT.items():
            srcs.setdefault(n, []).extend((ri, i) for i in ids)
    snks = {n:[("Out", i) for i in ids] for n, ids in goal_oT.items()}
    for ri, rule_iT in enumerate(rule_iTs):
        for n, ids in rule_iT.items():
            snks.setdefault(n, []).extend((ri, i) for i in ids)

    snk_list = []
    src_poss = []
    for n, n_snks in snks.items():
        snk_list += n_snks
        src_poss += [srcs[n] for _ in n_snks]


    #This strategy will produce invalid graphs
    #Easy filter to remove most of the bad connections
    def invalid_edge(src, snk):
        return ((src[0] == snk[0])) or ((src[0], snk[0]) == ("In", "Out"))
    def invalid_edges(src_list):
        return any(invalid_edge(src, snk) for src, snk in zip(src_list, snk_list))

    ds = []
    for src_list in it.product(*src_poss):
        if not invalid_edges(src_list):
            ds.append(list(zip(src_list, snk_list)))
    return ds

class Strat2Synth(Cegis):
    def __init__(
        self,
        comb_type,
        lhs_op_list: tp.List[Comb],
        rhs_op_list: tp.List[Comb],
    ):
        self.comb_type = comb_type
        lhs_cs = CombSynth(comb_type, lhs_op_list, prefix="l")
        rhs_cs = CombSynth(comb_type, rhs_op_list, prefix="r")
        self.lhs_cs = lhs_cs
        self.rhs_cs = rhs_cs

        P_inputs = [li==ri for li, ri in zip(lhs_cs.input_vars, rhs_cs.input_vars)]
        P_outputs = [lo==ro for lo, ro in zip(lhs_cs.output_vars, rhs_cs.output_vars)]

        And = fc.And
        #Final query:
        #  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)
        query = And([
            lhs_cs.P_wfp,
            rhs_cs.P_wfp,
            fc.Implies(
                And([
                    lhs_cs.P_lib,
                    lhs_cs.P_conn,
                    rhs_cs.P_lib,
                    rhs_cs.P_conn,
                ]),
                fc.Implies(
                    And(P_inputs),
                    And(P_outputs),
                )
            )
        ])
        #print(lhs_cs.P_wfp.serialize())
        E_vars = [*lhs_cs.E_vars, *rhs_cs.E_vars]
        super().__init__(query.to_hwtypes(), E_vars)


    def add_rule_cover(self, cover):
        from .symsel_synth import Rule
        cover: tp.List[tp.Tuple[Rule, int]] = cover
        rules = flat([[r for _ in range(cnt)] for r, cnt in cover])
        #Need to get type info for everthing
        #self_iT = comb_type_to_sT(self.comb_type[0])
        #self_oT = comb_type_to_sT(self.comb_type[1])

        #rule_iTs = [comb_type_to_sT(r.comb_type[0]) for r, _ in cover]
        #rule_oTs = [comb_type_to_sT(r.comb_type[1]) for r, _ in cover]

        #First goal: Enumerate over all the possible partitions.
        #for each rule, get the op dict count.
        lhs_rule_op_cnts = []
        rhs_rule_op_cnts = []
        for rule, rcnt in cover:
            lhs_op_cnt = {op: len(ids) for op, ids in rule.lhs_pat.op_dict.items()}
            rhs_op_cnt = {op: len(ids) for op, ids in rule.rhs_pat.op_dict.items()}
            for _ in range(rcnt):
                lhs_rule_op_cnts.append(lhs_op_cnt)
                rhs_rule_op_cnts.append(rhs_op_cnt)

        lhs_op_list = [op.qualified_name for op in self.lhs_cs.op_list]
        rhs_op_list = [op.qualified_name for op in self.rhs_cs.op_list]

        matches = []
        for lhs_rule_partions in enum_rule_partitions(lhs_op_list, lhs_rule_op_cnts):
            for rhs_rule_partions in enum_rule_partitions(rhs_op_list, rhs_rule_op_cnts):
                r_matchers = []
                for ri, rule in enumerate(rules):
                    lhs_ri_op_cnts = {op:cnts[ri] for op, cnts in lhs_rule_partions.items() if len(cnts[ri]) > 0}
                    rhs_ri_op_cnts = {op:cnts[ri] for op, cnts in rhs_rule_partions.items() if len(cnts[ri]) > 0}
                    lhs_matcher = match_pattern(rule.lhs_pat, self.lhs_cs, lhs_ri_op_cnts)
                    rhs_matcher = match_pattern(rule.rhs_pat, self.rhs_cs, rhs_ri_op_cnts)
                    r_matchers.append(it.product(lhs_matcher, rhs_matcher))
                for r_matches in it.product(*r_matchers):
                    l_insides = [m[0][0] for m in r_matches]
                    l_ins = [m[0][1] for m in r_matches]
                    l_outs = [m[0][2] for m in r_matches]
                    r_insides = [m[1][0] for m in r_matches]
                    r_ins = [m[1][1] for m in r_matches]
                    r_outs = [m[1][2] for m in r_matches]
                    for dag in enum_dags(self.lhs_cs.comb_type, rules):
                        ios = []
                        for d in dag:
                            (src, src_i), (snk, snk_i) = d
                            if src=="In":
                                l_src_lvar = src_i
                                r_src_lvar = src_i
                            else:
                                l_src_lvar = l_outs[src][src_i]
                                r_src_lvar = r_outs[src][src_i]
                            if snk == "Out":
                                l_snk_lvar = self.lhs_cs.output_lvars[snk_i]
                                r_snk_lvar = self.rhs_cs.output_lvars[snk_i]
                            else:
                                l_snk_lvar = l_ins[snk][snk_i]
                                r_snk_lvar = r_ins[snk][snk_i]
                            ios.append(fc.And([l_src_lvar == l_snk_lvar, r_src_lvar == r_snk_lvar]))
                        pat = fc.And([fc.And(l_insides), fc.And(r_insides), fc.And(ios)])
                        matches.append(pat)
        f_matches = fc.Or(matches)
        print(f"Excluded {len(matches)} Patterns")
        self.query = self.query & ~(f_matches.to_hwtypes())



    def gen_all_program_orders(self, sol):
        yield from it.product(
            self.lhs_cs.gen_all_program_orders(sol),
            self.rhs_cs.gen_all_program_orders(sol),
        )

    # Tactic. Generate all the non-permuted solutions.
    # For each of those solutions, generate all the permutations
    def gen_all_sols(self, opts=SolverOpts()):
        iTs, oTs = self.lhs_cs.comb_type
        def enum_fun(sol):
            #for sol in gen_input_perms(iTs, sol, self.lhs_cs.rhs_lvars, self.rhs_cs.rhs_lvars):
            #    sol = self.lhs_cs.fix_comm(sol)
            #    sol = self.rhs_cs.fix_comm(sol)
            #    yield sol
            for lhs_t_sol in self.lhs_cs.gen_all_program_orders(sol):
                for t_sol in self.rhs_cs.gen_all_program_orders(lhs_t_sol):
                    for sol in gen_input_perms(iTs, t_sol, self.lhs_cs.rhs_lvars, self.rhs_cs.rhs_lvars):
                        sol = self.lhs_cs.fix_comm(sol)
                        sol = self.rhs_cs.fix_comm(sol)
                        yield sol
        for i, sol in enumerate(self.cegis_all(opts, enum_fun=enum_fun)):
            #sols = flat([self.cs.gen_op_permutations(sol) for sol in sols])
            lhs_comb = self.lhs_cs.comb_from_solved(sol, name=QSym('solved', f"lhs_v{i}"))
            rhs_comb = self.rhs_cs.comb_from_solved(sol, name=QSym('solved', f"rhs_v{i}"))
            yield (lhs_comb, rhs_comb)


def gen_input_perms(iTs, sol, l_lvars, r_lvars):

    #Current issue. After swap, the commutative ops will be swapped

    def doit(from_ids, to_ids, lvars):
        i_to_lvars = {}
        for lvar in lvars:
            v = int(sol[lvar.value].constant_value())
            if v in from_ids:
                i_to_lvars.setdefault(v, []).append(lvar)
        assert len(i_to_lvars)==len(from_ids)
        vals = {i:sol[i_to_lvars[i][0].value] for i in from_ids}
        v_sols = [{v.value: vals[ti] for v in i_to_lvars[fi]} for fi, ti in zip(from_ids, to_ids)]

        new_sol = {}
        for d in v_sols:
            new_sol = {**new_sol, **d}
        return new_sol

    ivar_by_T = {}
    for i, T in enumerate(iTs):
        ivar_by_T.setdefault(str(T), []).append(i)
    assert len(ivar_by_T)==1
    from_ids = list(ivar_by_T.values())[0]
    for to_ids in it.permutations(from_ids):
        l_sols = doit(from_ids, to_ids, l_lvars)
        r_sols = doit(from_ids, to_ids, r_lvars)
        new_sol = {**sol, **l_sols, **r_sols}
        yield new_sol
    #yield sol
