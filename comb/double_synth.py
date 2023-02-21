from comb import Comb
from comb.ast import QSym
from comb.synth import Cegis, CombSynth, SolverOpts
import hwtypes.smt_utils as fc
import typing as tp

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
        lhs_cs = CombSynth(comb_type, lhs_op_list)
        rhs_cs = CombSynth(comb_type, rhs_op_list)
        self.lhs_cs = lhs_cs
        self.rhs_cs = rhs_cs

        P_inputs = [li==ri for li, ri in zip(lhs_cs.input_vars, rhs_cs.input_vars)]
        P_outputs = [lo==ro for lo, ro in zip(lhs_cs.output_vars, rhs_cs.output_vars)]

        And = fc.And
        #Final query:
        #  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)
        print(lhs_cs.P_wfp.serialize())
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

    # Tactic. Generate all the non-permuted solutions.
    # For each of those solutions, generate all the permutations
    def gen_all_sols(self, opts=SolverOpts()):
        for i, sol in enumerate(self.cegis_all(opts)):
            lhs_comb = self.lhs_cs.comb_from_solved(sol, name=QSym('solved', f"lhs_v{i}"))
            rhs_comb = self.rhs_cs.comb_from_solved(sol, name=QSym('solved', f"rhs_v{i}"))
            yield (lhs_comb, rhs_comb)


