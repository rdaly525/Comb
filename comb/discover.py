from .ast import QSym, Comb
from .stdlib import BitVectorModule
from .synth import SynthQuery, verify, flat
import typing as tp
import itertools as it

import more_itertools as mit

def discover_up_to_N(spec, maxN, op_names, const_list=(), max_iters=500):
    for N in range(1,maxN+1):
        print("-"*80)
        print("N=",N)
        res = discover(spec, N, op_names, const_list, max_iters)
        if len(res) > 0:
            return N, res
    return -1, []


#Iterate over all possible combinations of the op list
def discover(spec: Comb, N: int, op_list: tp.List[Comb], const_list = (), max_iters=500):

    all_combs = []
    all_indices = flat([[i for _ in range(N)] for i in range(len(op_list))])
    for indices in mit.distinct_combinations(all_indices, N):
        ops = [op_list[i] for i in indices]
        print("*"*80)
        op_str = "(" + ", ".join(str(op) for op in ops) + ")"
        print(f"Ops:{op_str}")
        sq = SynthQuery(spec, ops, const_list=const_list)
        combs = sq.gen_all_sols(max_iters=max_iters, verbose=True, permutations=False)
        all_combs += combs
    return all_combs