import dataclasses
import typing as tp

from more_itertools import distinct_combinations as multicomb
from comb import Comb
from .pattern import PatternEncoding, SymOpts
from .solver_utils import SolverOpts
from .spec_synth import SpecSynth
from .utils import flat, _list_to_counts, sub_cnts, ge0_cnts
import os

from ..frontend.compiler import compile_program

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/const.comb"

def pretty(spec, p, pi, s):
    print("*"*80)
    print(f"Found {pi} Pat: {s}")
    print(spec)
    print("     ----->")
    print(p.to_comb(), flush=True)


#Synthesizes Constants (0, 1)
#S
@dataclasses.dataclass
class ConstDiscover:
    irs: tp.List[Comb]
    maxIR: int
    opMax: tp.Mapping[int, int]
    pat_en_t: tp.Type[PatternEncoding]
    sym_opts: SymOpts = SymOpts()

    def __post_init__(self):
        assert issubclass(self.pat_en_t, PatternEncoding)
        with open(fname, 'r') as f:
            obj = compile_program(f.read())
        self.const_obj = obj
        if self.maxIR > 5:
            raise NotImplementedError()

    def gen_const_specs(self, vals=[0]):
        #TODO use the typing of everything
        N = 8
        ea_consts = [] #extra arg
        const_specs = {} #Good specs for constants
        for val in vals:
            const_specs[val] = self.const_obj.get("bad", f"c0")[(N,val)]
            ea_consts.extend(reversed([(self.const_obj.get("bad", f"c{i}")[(N,val)], val) for i in range(1, self.maxIR+2)]))
        return ea_consts, const_specs

    def gen_id_specs(self):
        #TODO use the typing of everything
        N = 16
        identities = list(reversed([self.const_obj.get("bad", f"id{i}")[N] for i in range(1, self.maxIR+2)]))
        return identities, self.const_obj.get('bad', f'id1')[N]

    def gen_all(self, const_vals = (0,), opts: SolverOpts = SolverOpts()):

        #ea = extra arguments
        ea_consts, const_specs = self.gen_const_specs(const_vals)
        ea_pats = {cval:[] for cval in const_vals}
        ea_ids, id_spec = self.gen_id_specs()
        id_pats = []
        #Synthesize constants
        pi = [0]

        def run(irs, opMax):
            for lN in range(1, self.maxIR+1):
                lhs_mc_ids = flat([[i for _ in range(opMax[i])] for i in range(len(irs))])
                for lhs_ids in multicomb(lhs_mc_ids, lN):
                    #print("K"*30,lhs_ids)
                    ir_ops = [irs[i] for i in lhs_ids]
                    #print([op.qualified_name for op in ir_ops])
                    ir_op_cnt = _list_to_counts([op.qualified_name for op in ir_ops])
                    exclude_pats = []
                    for pats in ([id_pats] + list(ea_pats.values())):
                        for pat in pats:
                            if ge0_cnts(sub_cnts(ir_op_cnt, pat.op_cnt)):
                                exclude_pats.append(pat)
                    for (ea_spec, cval) in ea_consts:
                        ss = SpecSynth(ea_spec, ir_ops, self.pat_en_t, self.sym_opts)
                        if not ss.pat_en.types_viable:
                            continue
                        for pat in exclude_pats:
                            ss.exclude_pattern(pat)
                        for sol, info in ss.cegis_all(opts):
                            pat = ss.pat_en.pattern_from_sol(sol)
                            #pretty(ea_spec, pat, pi, f"C{cval}")
                            ea_pats[cval].append(pat)
                            ss.exclude_pattern(pat)
                            exclude_pats.append(pat)
                            pi[0] +=1
                    for i, ea_spec in enumerate(ea_ids):
                        ss = SpecSynth(ea_spec, ir_ops, self.pat_en_t, self.sym_opts)
                        if not ss.pat_en.types_viable:
                            continue
                        for pat in exclude_pats:
                            ss.exclude_pattern(pat)
                        for sol, info in ss.cegis_all(opts):
                            pat = ss.pat_en.pattern_from_sol(sol)
                            #pretty(ea_spec, pat, pi, "ID")
                            id_pats.append(pat)
                            exclude_pats.append(pat)
                            ss.exclude_pattern(pat)
                            pi[0] +=1

        #Run first without constants
        run(self.irs, self.opMax)
        print("FIRST DOEN")
        #Now do the same thing but with the constants added to the IR spec
        #Only constants that have at least one pattern are added
        ea_pats = {c:pats for c, pats in ea_pats.items() if len(pats)>0}
        const_specs = {c:const_specs[c] for c in ea_pats}
        irs_w_const = self.irs + list(const_specs.values())
        num_ops = len(self.irs)
        opMax_w_const = {**self.opMax, **{i:1 for i in range(num_ops, num_ops+len(const_specs))}}
        run(irs_w_const, opMax_w_const)

        return (ea_pats, const_specs), id_pats

    #def gen_all_const(self, const_vals = [0], opts: SolverOpts = SolverOpts()):
    #    ea_consts, const_specs = self.gen_const_specs(const_vals)
    #    ea_pats = {cval:[] for cval in const_vals}
    #    #Synthesize constants
    #    pi = 0
    #    for (ea_spec, cval) in ea_consts:
    #        for lN in range(1, self.maxIR+1):
    #            lhs_mc_ids = flat([[i for _ in range(self.opMax[i])] for i in range(len(self.irs))])
    #            for lhs_ids in multicomb(lhs_mc_ids, lN):
    #                ir_ops = [self.irs[i] for i in lhs_ids]
    #                ir_op_cnt = _list_to_counts([op.qualified_name for op in ir_ops])
    #                ss = SpecSynth(ea_spec, ir_ops, self.pat_en_t, self.sym_opts)
    #                for e_cval, pats in ea_pats.items():
    #                    for pat in pats:
    #                        if ge0_cnts(sub_cnts(ir_op_cnt,pat.op_cnt)):
    #                            ss.exclude_pattern(pat)
    #                for sol, info in ss.cegis_all(opts):
    #                    pat = ss.pat_en.pattern_from_sol(sol)
    #                    ea_pats[cval].append(pat)
    #                    ss.exclude_pattern(pat)
    #                    pi +=1
    #    return ea_pats, const_specs

    #def gen_all_ids(self, opts: SolverOpts = SolverOpts()):
    #    ea_ids, id_spec = self.gen_id_specs()
    #    id_pats = []
    #    #Synthesize constants
    #    for ea_spec in ea_ids:
    #        for lN in range(1, self.maxIR+1):
    #            lhs_mc_ids = flat([[i for _ in range(self.opMax[i])] for i in range(len(self.irs))])
    #            for lhs_ids in multicomb(lhs_mc_ids, lN):
    #                ir_ops = [self.irs[i] for i in lhs_ids]
    #                ss = SpecSynth(ea_spec, ir_ops, self.pat_en_t, self.sym_opts)
    #                ir_op_cnt = _list_to_counts([op.qualified_name for op in ir_ops])
    #                for pat in id_pats:
    #                    if ge0_cnts(sub_cnts(ir_op_cnt,pat.op_cnt)):
    #                        ss.exclude_pattern(pat)
    #                for sol, info in ss.cegis_all(opts):
    #                    pat = ss.pat_en.pattern_from_sol(sol)
    #                    print("*"*80)
    #                    print("Found id Pat")
    #                    print(ea_spec)
    #                    print("     ----->")
    #                    print(pat.to_comb(), flush=True)
    #                    id_pats.append(pat)
    #                    ss.exclude_pattern(pat)
    #    return id_pats, id_spec
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
