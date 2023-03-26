import typing as tp

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import PatternEncoding, SymOpts, Pattern
from .solver_utils import SolverOpts, Cegis
from .utils import _make_list


class SpecSynth(Cegis):
    def __init__(
        self,
        spec: Comb,
        op_list: tp.List[Comb],
        pat_synth_t: tp.Type[PatternEncoding],
        sym_opts: SymOpts = SymOpts(),
        const_list: tp.Tuple[int] = (),
    ):
        assert issubclass(pat_synth_t, PatternEncoding)
        self.ps = pat_synth_t(spec.get_type(), op_list, const_list, sym_opts=sym_opts)
        self.spec = spec
        #Formal Spec (P_spec)
        P_spec = []
        for (i, ov) in enumerate(_make_list(self.spec.evaluate(*self.ps.input_vars))):
            P_spec.append(self.ps.output_vars[i] == ov)

        And = fc.And
        #Final query:
        #  Exists(L) Forall(V) P_wfp(L) & (P_lib & P_conn) => P_spec

        query = And([
            self.ps.P_sym,
            self.ps.P_wfp,
            fc.Implies(
                And([self.ps.P_lib, self.ps.P_conn]),
                And(P_spec)
            )
        ])
        print(query.serialize())
        E_vars = self.ps.E_vars
        super().__init__(query.to_hwtypes(), E_vars)


    def gen_all_sols(self, opts: SolverOpts = SolverOpts()) -> tp.List[Pattern]:
        pass
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
