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
        iTs, oTs = self.lhs_cs.comb_type
        l_comm_ids = [i for i, op in enumerate(self.lhs_cs.op_list) if op.commutative]
        r_comm_ids = [i for i, op in enumerate(self.rhs_cs.op_list) if op.commutative]
        def fix_comm(sol, comm_ids, op_in_lvars):
            sol = dict(sol)
            for i in comm_ids:
                lvars = op_in_lvars[i]
                lvals = [sol[lvar.value] for lvar in lvars]
                vals = sorted([(int(sol[lvar.value].constant_value()),li) for li, lvar in enumerate(lvars)])
                for si, (v, oi) in enumerate(vals):
                    sol[lvars[si].value] = lvals[oi]
            return sol

        def enum_fun(sol):
            #print("SOL" + "*"*80)
            #print("\n".join(f"{k}: {v}" for k, v in sol.items()))
            for sol in gen_input_perms(iTs, sol, self.lhs_cs.rhs_lvars, self.rhs_cs.rhs_lvars):
                sol = fix_comm(sol, l_comm_ids, self.lhs_cs.op_in_lvars)
                sol = fix_comm(sol, r_comm_ids, self.rhs_cs.op_in_lvars)
                #print("Fixed Sol")
                #print("\n".join(f"{k}: {v}" for k, v in sol.items()))
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
        #print("second Sol", from_ids, to_ids)
        #print("\n".join(f"{k}: {v}" for k, v in new_sol.items()))
        yield new_sol
    #yield sol
