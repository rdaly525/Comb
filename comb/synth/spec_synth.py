import typing as tp
import timeit

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import SymOpts, Pattern
from .pattern_encoding import PatternEncoding
from .solver_utils import SolverOpts, Cegis, IterLimitError
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
        simplify_dont_cares: bool,
        simplify_gen_consts: bool,
        spec_E_vars = []
    ):
        assert issubclass(pat_en_t, PatternEncoding)
        iT, oT = spec.get_type()
        iT = [type_to_nT(t) for t in iT]
        oT = [type_to_nT(t) for t in oT]
        pat_en = pat_en_t(iT, oT, op_list, simplify_dont_cares=simplify_dont_cares, simplify_gen_consts=simplify_gen_consts)
        assert pat_en.types_viable
        self.spec = spec
        self.pat_en = pat_en
        self.total_op_snks = sum(len(op.get_type()[0]) for op in op_list)
        self.total_dont_care_conn = pat_en.cnt_dont_care_conn(self.total_op_snks.bit_length())

        forall_vars = pat_en.forall_vars
        input_vars = pat_en.input_vars
        P_spec = []
        for (i, ov) in enumerate(_make_list(self.spec.evaluate(*input_vars))):
            P_spec.append(self.pat_en.output_vars[i] == ov)

        synth_base = fc.And([
            pat_en.assumptions,
            pat_en.P_iropt(*ir_opts),
            pat_en.P_narrow(*narrow_opts),
            pat_en.P_wfp,
        ])
        
        synth_constrain = fc.And([
            pat_en.constraints,
            pat_en.P_lib,
            pat_en.P_conn,
            fc.And(P_spec),
        ])

        verif = fc.And([
            pat_en.P_iropt(*ir_opts),
            pat_en.P_narrow(*narrow_opts),
            pat_en.P_wfp,
            fc.Implies(
                fc.And([
                    pat_en.P_lib,
                    pat_en.P_conn,
                ]),
                fc.And(P_spec)
            )
        ])
        E_vars = spec_E_vars + pat_en.E_vars
        super().__init__(synth_base.to_hwtypes(), synth_constrain.to_hwtypes(), verif.to_hwtypes(), E_vars, forall_vars)

    def exclude_pattern(self, pat:Pattern):
        m = self.pat_en.any_pat_match(pat)
        self.query = self.query & ~m.to_hwtypes()

    def gen_all_sols(self, opts: SolverOpts = SolverOpts()) -> tp.List[Pattern]:
        if not self.pat_en.types_viable:
            print("SPECSYNTH TYPES NOT VIABLE")
            return
        for sol, info in self.cegis_all(True, opts):
            yield self.pat_en.pattern_from_sol(sol)

    def CEGISAll_bin_search(self, E, LC, opts: SolverOpts):
        #do a binary search for the number of dont care connections
        self.enum_times = []
        stable_synth_base = self.synth_base
        maxcnt = self.total_op_snks
        for i in it.count(0):
            #both mincnt and maxcnt are inclusive
            mincnt = 0
            #maxcnt remains from previous iteration to make search space smaller
            best_sol, best_t = None, None
            while True:
                if mincnt == maxcnt and best_sol is not None:
                    #this early exit is not necessary but can save an extra iteration
                    break

                target = (mincnt + maxcnt + 1) // 2
                self.synth_base = stable_synth_base & (self.total_dont_care_conn >= target)
                sol,t = self.cegis(None, opts)

                if sol is not None and not isinstance(sol, IterLimitError):
                    best_sol, best_t = sol,t

                if mincnt == maxcnt:
                    break

                if sol is None or isinstance(sol, IterLimitError):
                    #no solution, lower maxcnt
                    maxcnt = target - 1
                else:
                    #solution found, raisecnt
                    mincnt = target

            if best_sol is None:
                break
            
            lhs_pat = self.pat_en.pattern_from_sol(best_sol)
            yield lhs_pat

            assert E
            if E:
                rp_cond, enum_time = self.patL(lhs_pat, {opi:opi for opi in range(len(self.pat_en.op_list))})
                stable_synth_base = stable_synth_base & ~rp_cond
                self.enum_times.append(enum_time)

    # E whether represents to exclude all equivalent rules
    def CEGISAll(self, E, LC, opts: SolverOpts):
        self.enum_times = []
        for i, (sol, t) in enumerate(self.cegis_all(exclude_prev=(not E), opts=opts)):
            lhs_pat = self.pat_en.pattern_from_sol(sol)
            yield lhs_pat

            assert E #or else we will just synthesize the same rules over and over
            if E:
                rp_cond, enum_time = self.patL(lhs_pat, {opi:opi for opi in range(len(self.pat_en.op_list))})
                self.synth_base = self.synth_base & ~rp_cond
                self.enum_times.append(enum_time)

    def patL(self, pat: Pattern, op_mapping, constrain_io = True):
        start = timeit.default_timer()
        cond = pat.patL(self.pat_en, op_mapping, constrain_io)
        delta = timeit.default_timer() - start
        return cond, delta
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
