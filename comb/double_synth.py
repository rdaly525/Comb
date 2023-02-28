from comb import Comb
from comb.ast import QSym
from comb.synth import Cegis, CombSynth, SolverOpts
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


class Strat2Synth(Cegis):
    def __init__(
        self,
        comb_type,
        lhs_op_list: tp.List[Comb],
        rhs_op_list: tp.List[Comb],
    ):
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
