from . import Comb
from .ast import QSym, BoolType, TypeCall, BVType, IntValue
from .synth import Cegis, CombSynth, SolverOpts, Pattern
from .utils import _list_to_counts, _list_to_dict, bucket_combinations

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

def comb_type_to_sT(T):
    Ns = []
    for t in T:
        if isinstance(t, BoolType):
            n = 0
        else:
            assert isinstance(t, TypeCall)
            assert isinstance(t.type, BVType)
            n = t.pargs[0].value
            assert isinstance(n, int)
            Ns.append(n)
    return _list_to_counts(Ns)


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
        E_vars = [*lhs_cs.E_vars, *rhs_cs.E_vars]
        super().__init__(query.to_hwtypes(), E_vars)


    def add_rule_cover(self, cover):
        from .symsel_synth import Rule
        cover: tp.List[tp.Tuple[Rule, int]] = cover
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
        for lhs_rule_partions in enum_rule_partitions(lhs_op_list, lhs_rule_op_cnts):
            for rhs_rule_partions in enum_rule_partitions(rhs_op_list, rhs_rule_op_cnts):
                print("%"*80)
                print(lhs_rule_partions)
                print(rhs_rule_partions)






        #pat = cover[0][0].lhs_pat

        #def gen_get_lvar(s: CombSynth):
        #    input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = s.lvars
        #    def get_lvar(id, aid, src=True):
        #        if id == "In":
        #            return input_lvars[aid]
        #        elif id == "Out":
        #            return output_lvars[aid]
        #        if src:
        #            lvars = op_out_lvars
        #        else:
        #            lvars = op_in_lvars
        #        op_idx = pat_idx_to_op_idx[id]
        #        return lvars[op_idx][aid]
        #    return get_lvar

        ##associate the ops in pat with the ops in lhs
        #pat_idx_to_op_idx = {}
        #input_lvars = []
        #output_lvars = []
        #l_get_lvar = gen_get_lvar(self.lhs_cs)
        #r_get_lvar = gen_get_lvar(self.rhs_cs)
        #edge_cons = []
        ##ai = argument index
        ##f = from
        ##t = to
        ##TODO separate out into 'interior' edges and IO edges
        ##foreach allocation of ops to each RR (do the product from both sides)
        ##   pattern match on each side. ie (input_lvars, interior_edge_conds, output_lvars)
        ##   for each enumerated pattern arangement
        ##       attach inputs/outputs of each pattern
        ##Interior edges constraint should be done independently for l pat and r pat
        ##exterior edges can be grouped together but simultaneously
        ##   ie ((l_lvar==l_pos_in0) & (r_lvar==r_pos_in0)) |
        ##      ((l_lvar==l_pos_in1) & (r_lvar==r_pos_in1)) |
        #for ((f_i, f_ai), (t_i, t_ai)) in pat.edges:
        #    f_lvar = l_get_lvar(f_i, f_ai, src=True)
        #    t_lvar = l_get_lvar(t_i, t_ai, src=False)
        #    edge_cons.append(f_lvar==t_lvar)


        #Given a set of rules
        raise NotImplementedError()













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


import pysmt.shortcuts as smt
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
