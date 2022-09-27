from .comb import QSym, Comb
from .modules import BitVectorModule
from .synth import SynthQuery, verify, flat
import typing as tp
import itertools as it

import more_itertools as mit

def discover_up_to_N(spec, maxN, op_names, const_list = ()):
    for N in range(1,maxN+1):
        res = discover(spec, N, op_names)
        if len(res) > 0:
            return N, res
    return -1, []


#Iterate over all possible combinations of the op list
def discover(spec: Comb, N: int, op_names: tp.List[QSym], const_list = ()):

    op_list = []
    for op in op_names:
        op_list.append(BitVectorModule().comb_from_sym(op))

    all_combs = []
    all_indices = flat([[i for _ in range(N)] for i in range(len(op_list))])
    for indices in mit.distinct_combinations(all_indices, N):
        ops = [op_list[i] for i in indices]
        print(*[op_names[i].name for i in indices])
        sq = SynthQuery(spec, ops, const_list=const_list)
        combs = sq.gen_all_sols(maxloops=5000, verbose=True, permutations=False)
        all_combs += combs
    return all_combs