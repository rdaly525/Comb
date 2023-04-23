import functools

from ..frontend.ast import Comb
from .solver_utils import Cegis, SolverOpts
from .pattern import Pattern, SymOpts, PatternEncoding
from .comb_encoding import CombEncoding
from .utils import _list_to_dict, bucket_combinations, flat, types_to_nTs, nT
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


def enum_dags(goal_iT, goal_oT, pats: tp.List[Pattern]):
    pat_iTs = [_list_to_dict(p.iT) for p in pats]
    pat_oTs = [_list_to_dict(p.oT) for p in pats]

    #Create a set of all sources/snks sorted by type
    srcs = {n:[(-1, i) for i in ids] for n, ids in _list_to_dict(goal_iT).items()}
    for pi, pat_oT in enumerate(pat_oTs):
        for n, ids in pat_oT.items():
            srcs.setdefault(n, []).extend((pi, i) for i in ids)
    snks = {n:[(len(pats), i) for i in ids] for n, ids in _list_to_dict(goal_oT).items()}
    for pi, pat_iT in enumerate(pat_iTs):
        for n, ids in pat_iT.items():
            snks.setdefault(n, []).extend((pi, i) for i in ids)


    #This strategy will produce invalid graphs
    #Easy filter to remove most of the bad connections
    def invalid_edge(src, snk):
        return ((src[0] == snk[0])) or ((src[0], snk[0]) == (-1, len(pats)))
    all_src = flat([srcs_ for srcs_ in srcs.values()])
    def invalid_dag(edges):
        used_srcs = set(src for src,_ in edges)
        all_used = all(src in used_srcs for src in all_src)
        bad_edge = any(invalid_edge(src, snk) for src, snk in edges)
        return (not all_used) or bad_edge
        #each source should be in edge list

    src_poss = []
    snk_list = []
    for n, n_snks in snks.items():
        snk_list += n_snks
        src_poss += [srcs[n] for _ in n_snks]

    graphs = []
    for src_list in it.product(*src_poss):
        edges = list(zip(src_list, snk_list))
        if not invalid_dag(edges):
            graphs.append(edges)
    return graphs

class RuleSynth(Cegis):
    def __init__(
        self,
        iT: tp.List[nT],
        oT: tp.List[nT],
        lhs_op_list: tp.List[Comb],
        rhs_op_list: tp.List[Comb],
        pat_en_t: tp.Type[PatternEncoding],
        sym_opts: SymOpts,
        only_lhs_sym: bool = False
    ):
        l_sym_opts = sym_opts
        if only_lhs_sym:
            r_sym_opts = SymOpts(False,False,False)
        else:
            r_sym_opts = SymOpts(sym_opts.comm, sym_opts.same_op, False)
        self.iT = iT
        self.oT = oT
        lhs_cs = pat_en_t(iT, oT, lhs_op_list, prefix="l", sym_opts=l_sym_opts)
        rhs_cs = pat_en_t(iT, oT, rhs_op_list, prefix="r", sym_opts=r_sym_opts)
        if lhs_cs.types_viable and rhs_cs.types_viable:
            self.lhs_cs = lhs_cs
            self.rhs_cs = rhs_cs

            P_inputs = [li==ri for li, ri in zip(lhs_cs.input_vars, rhs_cs.input_vars)]
            P_outputs = [lo==ro for lo, ro in zip(lhs_cs.output_vars, rhs_cs.output_vars)]

            #Final query:
            #  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)
            query = fc.And([
                lhs_cs.P_sym,
                rhs_cs.P_sym,
                lhs_cs.P_wfp,
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

            query = query.to_hwtypes()

            #wfp = fc.And([
            #    lhs_cs.P_sym,
            #    rhs_cs.P_sym,
            #    lhs_cs.P_wfp,
            #    rhs_cs.P_wfp,
            #])

            #xl = fc.And([lhs_cs.P_lib, lhs_cs.P_conn]).to_hwtypes()
            #xr = fc.And([rhs_cs.P_lib, rhs_cs.P_conn]).to_hwtypes()

            ##Substitute all of Ir and Or in xr with Il and Ol
            #subs = []
            #for Il, Ir in zip(lhs_cs.input_vars, rhs_cs.input_vars):
            #    subs.append((Il, Ir))
            ##for Ol, Or in zip(lhs_cs.output_vars, rhs_cs.output_vars):
            ##    subs.append((Ol, Or))
            #sub_xr = xr.substitute(*subs)
            #query = wfp.to_hwtypes() & (~(xl==sub_xr) | fc.And(P_outputs).to_hwtypes())

            #print(query.serialize())
            E_vars = [*lhs_cs.E_vars, *rhs_cs.E_vars]
            super().__init__(query, E_vars)

    #old one that used 'enum_patter_patrtions' to enumerate all same_op symmetries
    #def _match_pattern(self, p: Pattern, ri_op_ids):
    #    for pid_to_csid in enum_pattern_partitions(p, ri_op_ids):
    #        yield self.lhs_cs.match_one_pattern(p, pid_to_csid)

    #This enumerates all equiv patterns (from passed in pat) then matches on that
    def match_pattern(self, pat: Pattern, r_op_ids:tp.Mapping[str,tp.Iterable[int]]):
        ops = sorted(r_op_ids.keys())
        for p in pat.enum_all_equal():
            maps = [{pid:csid for pid,csid in zip(p.op_dict[op],r_op_ids[op])} for op in ops]
            pid_to_csid = functools.reduce(lambda d0, d1: {**d0, **d1}, maps)
            yield self.lhs_cs.match_one_pattern(p, pid_to_csid)






    #Note this is really only a LHS pat cover
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
