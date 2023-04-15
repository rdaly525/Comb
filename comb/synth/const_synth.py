import dataclasses
import typing as tp

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import PatternEncoding, SymOpts, Pattern
from .solver_utils import SolverOpts, Cegis
from .utils import _make_list, type_to_nT

#Synthesizes Constants (0, 1)
#S
@dataclasses.dataclass
class ConstDiscover:
    irs: tp.List[Comb]
    maxIR: int
    pat_en_t: tp.Type[PatternEncoding]
    sym_opts: SymOpts = SymOpts()

    def __post_init__(self):
        assert issubclass(self.pat_en_t, PatternEncoding)
        if self.maxIR > 3:
            raise NotImplementedError()

    def gen_all(self, opts: SolverOpts = SolverOpts()):

        for sol, info in self.cegis_all(opts):
            yield self.pat_en.pattern_from_sol(sol)
    # Tactic. Generate all the non-permuted solutions.
    # For each of those solutions, generate all the permutations
    #def gen_all_sols(self, permutations=False, opts: SolverOpts=SolverOpts()) -> tp.List[Comb]:
    #    sols = list(self.cegis_all(opts))
    #    for i, sol in enumerate(sols):
    #        print(f"{i}: {model_to_str(sol)}")

    #    if permutations:
    #        sols = flat([self.ps.gen_op_permutations(sol) for sol in sols])

    #    combs = [self.ps.comb_from_solved(sol, name=QSym('Solved', f"v{i}")) for i, sol in enumerate(sols)]
    #    #if len(set(c.serialize_body() for c in combs)) != len(combs):
    #    #    c0 = combs[0].serialize_body()
    #    #    for i in range(1, len(combs)):
    #    #        if c0 == combs[i].serialize_body():
    #    #            print(f"BAD!, 0 = {i}")
    #    #            print(combs[0])
    #    #            print(combs[i])
    #    #            print(f"0:", sols[0])
    #    #            print(f"{i}:", sols[i])
    #    #    raise ValueError("Somehting went wrong")
    #    return combs
