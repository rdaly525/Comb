import typing as tp

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import SymOpts, Pattern
from .pattern_encoding import PatternEncoding
from .solver_utils import SolverOpts, Cegis
from .utils import _make_list, type_to_nT, _list_to_dict
import itertools as it

class SpecSynth(Cegis):
    def __init__(
        self,
        spec: Comb,
        op_list: tp.List[Comb],
        pat_en_t: tp.Type[PatternEncoding],
        ir_opts: tp.Tuple[int],
        narrow_opts: tp.Tuple[int],
        const_list: tp.Tuple[int] = (),
    ):
        assert issubclass(pat_en_t, PatternEncoding)
        iT, oT = spec.get_type()
        iT = [type_to_nT(t) for t in iT]
        oT = [type_to_nT(t) for t in oT]
        self.pat_en = pat_en_t(iT, oT, op_list, const_list)
        if self.pat_en.types_viable:
            self.spec = spec
            input_vars = self.pat_en.input_vars
            #Formal Spec (P_spec)
            P_spec = []
            for (i, ov) in enumerate(_make_list(self.spec.evaluate(*input_vars))):
                P_spec.append(self.pat_en.output_vars[i] == ov)
            And = fc.And
            #Final query:
            #  Exists(L) Forall(V) P_wfp(L) & (P_lib & P_conn) => P_spec


            synth_base = And([
                self.pat_en.P_iropt(*ir_opts),
                self.pat_en.P_narrow(*narrow_opts),
                self.pat_en.P_wfp,
            ])

            synth_constrain = And([
                self.pat_en.P_lib, 
                self.pat_en.P_conn,
                And(P_spec)
            ])

            verif = And([
                self.pat_en.P_iropt(*ir_opts),
                self.pat_en.P_narrow(*narrow_opts),
                self.pat_en.P_wfp,
                fc.Implies(
                    And([self.pat_en.P_lib, self.pat_en.P_conn]),
                    And(P_spec)
                )
            ])

            #print(query.serialize())
            E_vars = self.pat_en.E_vars
            super().__init__(synth_base.to_hwtypes(), synth_constrain.to_hwtypes(), verif.to_hwtypes(), E_vars, input_vars)


    def exclude_pattern(self, pat:Pattern):
        m = self.pat_en.any_pat_match(pat)
        self.query = self.query & ~m.to_hwtypes()

    def gen_all_sols(self, opts: SolverOpts = SolverOpts()) -> tp.List[Pattern]:
        if not self.pat_en.types_viable:
            print("SPECSYNTH TYPES NOT VIABLE")
            return
        for sol, info in self.cegis_all(True, opts):
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
