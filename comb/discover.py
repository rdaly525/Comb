import dataclasses

from .ast import QSym, Comb, TypeCall, BVType, IntValue
from .double_synth import Strat2Synth
from .stdlib import BitVectorModule
from .synth import BuckSynth, verify, SolverOpts
from .utils import flat
import typing as tp
import itertools as it

import more_itertools as mit

def discover_up_to_N(spec, maxN, op_names, const_list=(), opts=SolverOpts()):
    for N in range(1,maxN+1):
        print("-"*80)
        print("N=",N)
        res = discover(spec, N, op_names, const_list, opts)
        if len(res) > 0:
            return N, res
    return -1, []


#Iterate over all possible combinations of the op list
def discover(spec: Comb, N: int, op_list: tp.List[Comb], const_list = (), opts=SolverOpts()):

    all_combs = []
    all_indices = flat([[i for _ in range(N)] for i in range(len(op_list))])
    for indices in mit.distinct_combinations(all_indices, N):
        ops = [op_list[i] for i in indices]
        print("*"*80)
        op_str = "(" + ", ".join(str(op) for op in ops) + ")"
        print(f"Ops:{op_str}")
        sq = BuckSynth(spec, ops, const_list=const_list)
        combs = sq.gen_all_sols(permutations=False, opts=opts)
        all_combs += combs
    return all_combs


def discover_strat2(
    lhs: tp.List[Comb],
    rhs: tp.List[Comb],
    ranges,
    N,
    opts
):
    rI, rO, rL, rR = ranges
    BVN = TypeCall(BVType(), [IntValue(N)])
    for iN, oN in it.product(rI, rO):
        iT = [BVN for _ in range(iN)]
        oT = [BVN for _ in range(oN)]
        for lN, rN in it.product(rL, rR):
            yield from _discover_strat2(lhs, rhs, lN, rN, (iT, oT), opts=opts)

#Iterate over all possible combinations of the op list
def _discover_strat2(
    lhs: tp.List[Comb],
    rhs: tp.List[Comb],
    lN: int,
    rN: int,
    T,
    opts=SolverOpts(),
):
    iT, oT = T
    lhs_indices = flat([[i for _ in range(lN)] for i in range(len(lhs))])
    rhs_indices = flat([[i for _ in range(rN)] for i in range(len(rhs))])
    multicomb = mit.distinct_combinations
    for (lhs_id, rhs_id) in it.product(multicomb(lhs_indices, lN), multicomb(rhs_indices, rN)):
        lhs_ops = [lhs[i] for i in lhs_id]
        rhs_ops = [rhs[i] for i in rhs_id]
        print("*"*80)
        op_strs = ["[" + ", ".join(str(op.name) for op in ops) + "]" for ops in (lhs_ops, rhs_ops)]
        print(f"{op_strs[0]} -> {op_strs[1]}")

        ss = Strat2Synth(
            comb_type=(iT, oT),
            lhs_op_list=lhs_ops,
            rhs_op_list=rhs_ops,
        )
        yield from ss.gen_all_sols(opts=opts)