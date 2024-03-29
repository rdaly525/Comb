import functools
import timeit

from ..frontend.ast import Comb
from .solver_utils import Cegis, SolverOpts
from .pattern import Pattern, enum_dags
from .pattern_encoding import PatternEncoding
from .comb_encoding import CombEncoding
from .utils import _list_to_dict, bucket_combinations, flat, nT
from .rule import Rule

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
    if set(p.op_names) != set(partitions.keys()):
        raise ValueError()
    product_ids = []
    for op, p_ids in _list_to_dict(p.op_names).items():
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


def match_one_pattern(p: Pattern, cs: CombEncoding, pid_to_csid: tp.Mapping[int, int]):
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
        assert li == -1
        assert ri != p.num_ops
        r_lvar = cs.op_in_lvars[pid_to_csid[ri]][rai]
        in_lvars[lai] = r_lvar
    out_lvars = {}
    for (li, lai), (ri, rai) in p.out_edges:
        assert ri == p.num_ops
        assert li != -1
        l_lvar = cs.op_out_lvars[pid_to_csid[li]][lai]
        out_lvars[lai] = l_lvar
    return fc.And(interior_edges), in_lvars, out_lvars


class RuleSynth(Cegis):
    def __init__(
        self,
        iT: tp.List[nT],
        oT: tp.List[nT],
        lhs_op_list: tp.List[Comb],
        rhs_op_list: tp.List[Comb],
        ir_opts,
        narrow_opts,
        pat_en_t: tp.Type[PatternEncoding],
    ):
        self.iT = iT
        self.oT = oT
        lhs_cs = pat_en_t(iT, oT, lhs_op_list, prefix="l")
        rhs_cs = pat_en_t(iT, oT, rhs_op_list, prefix="r")
        assert lhs_cs.types_viable and rhs_cs.types_viable
        self.lhs_cs = lhs_cs
        self.rhs_cs = rhs_cs
        self.enum_times = []
        self.ir_opts = ir_opts
        self.narrow_opts = narrow_opts

        input_vars = [*lhs_cs.input_vars, *rhs_cs.input_vars]
        P_inputs = [li==ri for li, ri in zip(lhs_cs.input_vars, rhs_cs.input_vars)]
        P_outputs = [lo==ro for lo, ro in zip(lhs_cs.output_vars, rhs_cs.output_vars)]

        #Final query:
        #  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)
        synth_base = fc.And([
            lhs_cs.P_iropt(*ir_opts),
            lhs_cs.P_narrow(*narrow_opts),
            lhs_cs.P_wfp,
            rhs_cs.P_iropt(*ir_opts),
            #we dont want to constrain the output order of the rhs, since that could
            #make certain rules we want unsynthesizable
            rhs_cs.P_narrow(*narrow_opts[:-1], 0),
            rhs_cs.P_wfp,
        ])

        synth_constrain = fc.And([
            lhs_cs.P_lib,
            lhs_cs.P_conn,
            rhs_cs.P_lib,
            rhs_cs.P_conn,
            fc.And(P_outputs),
        ])

        verif = fc.And([
            lhs_cs.P_iropt(*ir_opts),
            lhs_cs.P_narrow(*narrow_opts),
            lhs_cs.P_wfp,
            rhs_cs.P_iropt(*ir_opts),
            rhs_cs.P_narrow(*narrow_opts[:-1], 0), #see above comment
            rhs_cs.P_wfp,
            fc.Implies(
                fc.And([
                    lhs_cs.P_lib,
                    lhs_cs.P_conn,
                    rhs_cs.P_lib,
                    rhs_cs.P_conn,
                ]),
                fc.Implies(
                    fc.And(P_inputs),
                    fc.And(P_outputs),
                )
            )
        ])
        #print(query.serialize())
        #assert 0
        E_vars = [*lhs_cs.E_vars, *rhs_cs.E_vars]
        super().__init__(synth_base.to_hwtypes(), synth_constrain.to_hwtypes(), verif.to_hwtypes(), E_vars, input_vars)


    # E whether represents to exclude all equivalent rules
    def CEGISAll(self, E, LC, opts: SolverOpts):
        self.enum_times = []
        for i, (sol, t) in enumerate(self.cegis_all(exclude_prev=(not E), opts=opts)):
            lhs_pat = self.lhs_cs.pattern_from_sol(sol)
            rhs_pat = self.rhs_cs.pattern_from_sol(sol)
            rule = Rule(lhs_pat, rhs_pat, i, t)
            yield rule
            if E:
                #Exclude full rule.
                if LC:
                    rp_cond, enum_time = self.patL(rule.lhs)
                else:
                    rp_cond, enum_time = self.ruleL(rule)
                self.enum_times.append(enum_time)
                self.synth_base = self.synth_base & ~rp_cond

    def ruleL(self, rule:Rule):
        L_IR = self.lhs_cs.L
        L_ISA = self.rhs_cs.L
        start = timeit.default_timer()
        rule_cond = rule.ruleL(L_IR, L_ISA)
        delta = timeit.default_timer() - start
        return rule_cond, delta

    #Only for IR pattern
    def patL(self, pat: Pattern):
        L_IR = self.lhs_cs.L
        start = timeit.default_timer()
        pat_cond = pat.patL(L_IR)
        delta = timeit.default_timer() - start
        return pat_cond, delta

    #old one that used 'enum_patter_patrtions' to enumerate all same_op symmetries
    #def _match_pattern(self, p: Pattern, ri_op_ids):
    #    for pid_to_csid in enum_pattern_partitions(p, ri_op_ids):
    #        yield self.lhs_cs.match_one_pattern(p, pid_to_csid)

    #This enumerates all equiv patterns (from passed in pat) then matches on that
    #DEPRECATED
    def match_pattern(self, pat: Pattern, r_op_ids:tp.Mapping[str,tp.Iterable[int]]):
        ops = sorted(r_op_ids.keys())
        for p in pat.enum_all_equal():
            maps = [{pid:csid for pid,csid in zip(p.op_dict[op],r_op_ids[op])} for op in ops]
            pid_to_csid = functools.reduce(lambda d0, d1: {**d0, **d1}, maps)
            yield self.lhs_cs.match_one_pattern(p, pid_to_csid)






    #Note this is really only a LHS pat cover
    #DEPRECATED
    def add_rule_cover(self, cover: tp.List[tp.Tuple[Pattern, int]]):
        pats = flat([[p for _ in range(cnt)] for p, cnt in cover])

        #First goal: Enumerate over all the possible partitions.
        #for each rule, get the op dict count.
        lhs_rule_op_cnts = []
        for pat, rcnt in cover:
            lhs_op_cnt = pat.op_cnt
            for _ in range(rcnt):
                lhs_rule_op_cnts.append(lhs_op_cnt)
        assert len(lhs_rule_op_cnts) == len(pats)

        lhs_op_list = [op.qualified_name for op in self.lhs_cs.op_list]

        matches = []
        for lhs_rule_partions in enum_rule_partitions(lhs_op_list, lhs_rule_op_cnts):
            matchers = []
            for pi, pat in enumerate(pats):
                lhs_ri_op_ids = {op:cnts[pi] for op, cnts in lhs_rule_partions.items() if len(cnts[pi]) > 0}
                lhs_matcher = self.match_pattern(pat, lhs_ri_op_ids)
                matchers.append(lhs_matcher)
            for r_matches in it.product(*matchers):
                for dag in enum_dags(self.iT, self.oT, pats):
                    match = self.lhs_cs.match_rule_dag(dag, r_matches)
                    matches.append(match)
        f_matches = fc.Or(matches)
        print(f"Excluded Cover Patterns: {len(matches)}")
        self.query = self.query & ~(f_matches.to_hwtypes())

    def exclude_pattern(self, lhs_pat:Pattern):
        m = self.lhs_cs.any_pat_match(lhs_pat)
        self.query = self.query & ~m.to_hwtypes()



    #def gen_all_program_orders(self, sol):
    #    yield from it.product(
    #        self.lhs_cs.gen_all_program_orders(sol),
    #        self.rhs_cs.gen_all_program_orders(sol),
    #    )

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
