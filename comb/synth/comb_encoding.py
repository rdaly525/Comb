import collections
import functools
import itertools as it

from hwtypes import SMTBitVector as SBV
import networkx as nx
from hwtypes import smt_utils as fc
import hwtypes as ht
from ..frontend.ast import QSym, Sym, TypeCall, BVType, InDecl, OutDecl
from ..frontend.ir import AssignStmt, CombProgram
from ..frontend.stdlib import make_bv_const, CBVSynthConst, CBVDontCare, BVDontCare, is_dont_care
from .pattern import Pattern
from .pattern_encoding import PatternEncoding
from .solver_utils import get_var
from .utils import flat, _to_int, _list_to_dict, type_to_nT, nT_to_type
from hwtypes import SMTBitVector as SBV
import typing as tp


VarPair = collections.namedtuple('VarPair', 'lvar, var')

#This is the Gulwani Encoding
class CombEncoding(PatternEncoding):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        hard_consts = []
        tot_locs = len(self.input_vars) + len(hard_consts) + sum([len(ovs) for ovs in self.op_out_vars])
        lvar_t_width = tot_locs
        self.lvar_t = SBV[lvar_t_width]

        #These can be hardcoded
        self.input_lvars = list(range(len(self.input_vars)))
        Ninputs = len(self.input_vars)

        #hard_const_lvars = list(range(Ninputs, Ninputs +len(self.hard_consts)))
        hard_const_lvars = list(range(Ninputs, Ninputs +len(hard_consts)))
        op_out_lvars = []
        op_in_lvars = []
        synth_vars = []
        synth_map = {}
        dont_care_vars = []
        hardcoded_lvars = len(self.input_vars) + len(hard_consts)
        assumptions = [ht.SMTBit(1)]
        dont_care_map = {}

        for opi, op in enumerate(self.op_list):
            op_iTs, op_oTs = op.get_type()
            if isinstance(op.comb, CBVSynthConst):
                assert len(op_oTs) == 1
                var = get_var(f"{self.prefix}_synth_const_op[{opi}]", op_oTs[0])
                synth_vars.append(var)
                synth_map[opi] = var
                op.eval = functools.partial(op.eval, var)
            elif isinstance(op.comb, BVDontCare):
                assert len(op_oTs) == 1
                var = get_var(f"{self.prefix}_dont_care_op[{opi}]", op_oTs[0])
                dont_care_vars.append(var)
                op.eval = functools.partial(op.eval, var)
                dont_care_map.setdefault(op_oTs[0], []).append(var)
            elif isinstance(op.comb, CBVDontCare):
                assert len(op_oTs) == 1
                var = get_var(f"{self.prefix}_c_dont_care_op[{opi}]", op_oTs[0])
                dont_care_vars.append(var)
                op.eval = functools.partial(op.eval, var)

            if len(op_iTs) == 0:
                out_lvars = []
                for i, T in enumerate(op_oTs):
                    v = get_var(f"{self.prefix}_L_op[{opi}]_out[{i}]", lvar_t_width)
                    out_lvars.append(v)
                    assumptions.append(v == hardcoded_lvars)
                    hardcoded_lvars += 1
                    if is_dont_care(op.comb):
                        dont_care_map.setdefault(type_to_nT(T), []).append(v)
                op_in_lvars.append([])
                op_out_lvars.append(out_lvars)
            else:
                op_in_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_in[{i}]", lvar_t_width) for i, T in enumerate(op_iTs)])
                op_out_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_out[{i}]", lvar_t_width) for i, T in enumerate(op_oTs)])
            
        output_lvars = [get_var(f"{self.prefix}_L_out[{i}]", lvar_t_width) for i in range(len(self.output_vars))]
        self.op_in_lvars = op_in_lvars
        self.op_out_lvars = op_out_lvars
        self.output_lvars = output_lvars
        self.synth_vars = synth_vars
        self.synth_map = synth_map
        self.dont_care_vars = dont_care_vars
        self.dont_care_map = dont_care_map
        self.assumptions = fc.And(assumptions)

        # each op might have unique constraints, such as the enum constraints for PE instructions
        constraints = [ht.SMTBit(1)]
        for op,in_lvars,out_lvars,in_vars,out_vars in zip(self.op_list, self.op_in_lvars, self.op_out_lvars, self.op_in_vars, self.op_out_vars):
            if op.constraints is not None:
                constraints.append(op.constraints(in_lvars, out_lvars, in_vars, out_vars))

        self.constraints = fc.And(constraints)

        #get list of lvars (existentially quantified in final query)
        self.E_vars = output_lvars + flat(op_out_lvars) + flat(op_in_lvars) + synth_vars
        self.forall_vars = self.input_vars + dont_care_vars
        self.lvars = (self.input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars)
        self.rhs_lvars = flat(op_in_lvars) + output_lvars
        self.Ninputs = Ninputs
        self.Nconsts = 0
        self.tot_locs = tot_locs

        self.op_to_sorted_snks = {} #Used to save the symmetry orderings
        self.src_n = {n: {(-1,id):VarPair(self.input_lvars[id], self.input_vars[id]) for id in ids} for n, ids in _list_to_dict(self.iT).items()}
        self.snk_n = {n: {(self.num_ops,id):VarPair(self.output_lvars[id], self.output_vars[id]) for id in ids} for n, ids in _list_to_dict(self.oT).items()}
        for opi, op in enumerate(self.op_list):
            iT, oT = op.get_type()
            iT = [type_to_nT(t) for t in iT]
            oT = [type_to_nT(t) for t in oT]
            for n, ids in _list_to_dict(iT).items():
                self.snk_n.setdefault(n, {}).update({(opi, id):VarPair(self.op_in_lvars[opi][id], self.op_in_vars[opi][id]) for id in ids})
            for n, ids in _list_to_dict(oT).items():
                self.src_n.setdefault(n, {}).update({(opi, id):VarPair(self.op_out_lvars[opi][id], self.op_out_vars[opi][id]) for id in ids})

    def cnt_dont_care_conn(self, num_bits):
        zero = SBV[num_bits](0)
        one = SBV[num_bits](1)

        cnt = zero
        for T,d in self.snk_n.items():
            for (opi,_),(snk_lvar,_) in d.items():
                if opi == self.num_ops:
                    continue
                if T not in self.dont_care_map:
                    continue
                dont_care_src_lvars = self.dont_care_map[T]
                match = [snk_lvar == src_lvar for src_lvar in dont_care_src_lvars]
                match = fc.Or(match).to_hwtypes()
                cnt = cnt + match.ite(one, zero)
        return cnt

    @property
    def L(self):
        return self.input_lvars, self.output_lvars, self.op_in_lvars, self.op_out_lvars

    @property
    def P_conn(self):
        P_conn = []
        for n, src_dict in self.src_n.items():
            snk_dict = self.snk_n.get(n,{})
            for src_v, snk_v in it.product(src_dict.values(), snk_dict.values()):
                P_conn.append(fc.Implies(src_v.lvar==snk_v.lvar, src_v.var==snk_v.var))
        return fc.And(P_conn)

    @property
    def P_in_range(self):
        # Temp locs and output locs are in range of temps
        flat_op_out_lvars = flat(self.op_out_lvars)
        P_in_range = []
        for lvar in flat_op_out_lvars:
            P_in_range.append(fc.And([lvar>=self.Ninputs + self.Nconsts, lvar < self.tot_locs]))

        #op in locs and outputs are in range(0,tot)

        for lvar in self.rhs_lvars:
            P_in_range.append(lvar < self.tot_locs)

        #output loc cannot be inputs
        for lvar in self.output_lvars:
           P_in_range.append(lvar >= self.Ninputs + self.Nconsts)

        return fc.And(P_in_range)

    @property
    def P_out_unique(self):
        P_out_unique = []
        for lvar_a, lvar_b in it.combinations(self.output_lvars, 2):
            P_out_unique.append(lvar_a != lvar_b)
        return fc.And(P_out_unique)

    @property
    def P_loc_unique(self):
        # Temp locs are unique
        #Could simplify to only the first lhs of each stmt
        flat_op_out_lvars = flat(self.op_out_lvars)
        P_loc_unique = []
        for lvar_a, lvar_b in it.combinations(flat_op_out_lvars, 2):
            P_loc_unique.append(lvar_a != lvar_b)
        return fc.And(P_loc_unique)

    @property
    def P_multi_out(self):
        # multi outputs are off by 1
        P_multi_out = []
        for lvars in self.op_out_lvars:
            for i, lv1 in enumerate(lvars[1:]):
                P_multi_out.append(lvars[0]+1+i == lv1)
        return fc.And(P_multi_out)

    @property
    def P_acyc(self):
        P_acyc = []
        # ACYC Constraint
        #  op_out_lvars[i] > op_in_lvars[i]
        for o_lvars, i_lvars in zip(self.op_out_lvars, self.op_in_lvars):
            #thanks to P_multi_out, only need to ensure ivars are < first ovar
            P_acyc += [o_lvars[0] > ilvar for ilvar in i_lvars]
        return fc.And(P_acyc)

    #Restricts snks to only allow for same type sources
    @property
    def P_well_typed(self):
        src_lvars_T = {T:[(opi,lvar) for (opi,_), (lvar, _) in vard.items()] for T,vard in self.src_n.items()}
        snk_lvars_T = {T:[(opi,lvar) for (opi,_), (lvar, _) in vard.items()] for T,vard in self.snk_n.items()}
        well_typed = []
        for T, snk_lvars in snk_lvars_T.items():
            assert T in src_lvars_T
            src_lvars = src_lvars_T[T]
            if T.const and self.simplify_gen_consts:
                # here we constrain each constant sink to only connect to an input or ONE constant synthesis operation
                # assume the program has no constant outputs
                assert all(opi < self.num_ops for opi,_ in snk_lvars)

                snk_lvars = [lvar for _,lvar in snk_lvars]
                src_lvars_inputs = [lvar for (opi, lvar) in src_lvars if opi == -1]
                src_lvars_dont_cares = [lvar for (opi, lvar) in src_lvars if opi != -1 and is_dont_care(self.op_list[opi].comb)]
                src_lvars_synth_consts = [lvar for (opi, lvar) in src_lvars if opi != -1 and not is_dont_care(self.op_list[opi].comb)]
                if self.simplify_dont_cares:
                    assert len(src_lvars_dont_cares) == 1

                # each snk gets its own unique src, so the length of the snks and constant synthesis sources must be equal
                assert len(snk_lvars) == len(src_lvars_synth_consts)
                for snk_lvar, src_lvar_synth_const in zip(snk_lvars, src_lvars_synth_consts):
                    valid_conn = src_lvars_inputs + src_lvars_dont_cares + [src_lvar_synth_const]
                    well_typed.append(fc.Or([lvar==snk_lvar for lvar in valid_conn]))
            else:
                for _,snk_lvar in snk_lvars:
                    well_typed.append(fc.Or([src_lvar==snk_lvar for _,src_lvar in src_lvars]))

        return fc.And(well_typed)

    #Every pairwise same op needs to have distinct inputs
    @property
    def P_cse(self):
        op_ids = _list_to_dict([op.qualified_name for op in self.op_list])
        P_cse = []
        for op, ids in op_ids.items():
            if len(ids)<2:
                continue
            elif is_dont_care(self.op_list[ids[0]].comb):
                continue
            elif isinstance(self.op_list[ids[0]].comb, CBVSynthConst):
                # if simplify_gen_consts is set, we don't care about duplicate constants
                if not self.simplify_gen_consts:
                    for i0, i1 in it.combinations(ids, 2):
                        P_cse.append(self.synth_map[i0] != self.synth_map[i1])
                continue
            else:
                for i0, i1 in it.combinations(ids, 2):
                    P_cse.append(fc.Or([lv0!=lv1 for lv0, lv1 in zip(self.op_in_lvars[i0], self.op_in_lvars[i1])]))
        return fc.And(P_cse)

    @property
    def P_dse(self):
        def rhss():
            for lvar in flat(self.op_in_lvars):
                yield lvar
            for lvar in self.output_lvars:
                yield lvar

        #All vars are used
        used = self.lvar_t(0)
        for lvar_rhs in rhss():
            used |= (self.lvar_t(1) << lvar_rhs)
        
        mask = 2**(self.Ninputs + self.Nconsts)-1
        P_used = (used & mask) == mask

        for lvars, op in zip(self.op_out_lvars, self.op_list):
            if self.simplify_dont_cares and is_dont_care(op.comb):
                continue
            if self.simplify_gen_consts and isinstance(op.comb, CBVSynthConst):
                continue
            mask = self.lvar_t(2**len(lvars)-1) << lvars[0]
            P_used &= ((used & mask) != 0)
        return P_used


    @property
    def P_comm(self):
        #Strict ordering on arguments of commutative ops
        P_comm = []
        for i, op in enumerate(self.op_list):
            for arg_ids in op.comm_info:
                assert sorted(arg_ids) == arg_ids
                arg_lvars = [self.op_in_lvars[i][ai] for ai in arg_ids]
                for lv0, lv1 in  zip(arg_lvars[:-1], arg_lvars[1:]):
                    P_comm.append(lv0 <= lv1)
        return fc.And(P_comm)

    @property
    def P_K(self):
        #Strict ordering on same-kind ops
        P_K = []
        ops = _list_to_dict([op.qualified_name for op in self.op_list])
        for op_name, op_ids in ops.items():
            if len(op_ids) ==1:
                continue
            #thanks to P_multi_out, only need to comparison with first ovars
            o_lvars = [self.op_out_lvars[i][0] for i in op_ids]
            for lv0, lv1 in zip(o_lvars[:-1], o_lvars[1:]):
                P_K.append(lv0 < lv1)

        return fc.And(P_K)

    @property
    def P_wfp(self):
        P_wfp = [
            self.P_in_range,
            self.P_loc_unique,
            self.P_multi_out,
            self.P_well_typed,
            self.P_acyc,
            self.P_out_unique,
        ]
        return fc.And(P_wfp)



    #@property
    #def P_sym_input_perm(self):
    #    assert self.sym_opts.input_perm
    #    input_T = _list_to_dict(self.iT)

    #    # Create a set of all sources/snks sorted by type
    #    P_perms = []
    #    for n, ids in input_T.items():
    #        snk_dict = self.snk_n[n]
    #        src_dict = self.src_n[n]
    #        snks = sorted(snk_dict.keys())
    #        P_perm = []
    #        used = [ht.SMTBit(0) for _ in ids]
    #        for snk in snks:
    #            snk_lvar = snk_dict[snk].lvar
    #            lvars = [snk_lvar == src_dict[(-1, id)].lvar for id in ids]
    #            i_perm = []
    #            for ui, u in enumerate(used[:-1]):
    #                i_perm.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
    #            used = [u | lvars[ui] for ui, u in enumerate(used)]
    #            P_perm.append(fc.And(i_perm))
    #        P_perms.append(fc.And(P_perm))
    #    ret = fc.And(P_perms)
    #    return ret

    #def fix_comm(self, sol):
    #    comm_ids = [i for i, op in enumerate(self.op_list) if op.comm_info]
    #    v_sols = []
    #    for i in comm_ids:
    #        lvars = self.op_in_lvars[i]
    #        lvals = [sol[lvar.value] for lvar in lvars]
    #        vals = sorted([(int(sol[lvar.value].constant_value()), li) for li, lvar in enumerate(lvars)])
    #        v_sols.append({lvars[si].value: lvals[oi] for si, (v, oi) in enumerate(vals)})

    #    new_sol = dict(sol)
    #    for d in v_sols:
    #        new_sol = {**new_sol, **d}
    #    return new_sol


    #def gen_all_program_orders(self, sol):
    #    input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
    #    #Create Graph from sol
    #    lvar_to_nid = {}
    #    int_to_lval = {}
    #    for v in input_lvars:
    #        lvar_to_nid[v] = 'In'
    #    assert len(hard_const_lvars) == 0
    #    ln_to_nid = {}

    #    nids = []
    #    for li, lvars in enumerate(op_out_lvars):
    #        tmp_vals = tuple(_to_int(sol[lvar.value]) for lvar in lvars)
    #        nid = tmp_vals
    #        nids.append((tmp_vals[0], nid))
    #        ln_to_nid[li] = nid
    #        for v, lvar in zip(tmp_vals, lvars):
    #            lvar_to_nid[v] = nid
    #            int_to_lval[v] = sol[lvar.value]
    #    nids = ["In"] + [v for _, v in sorted(nids)] + ["Out"]
    #    g = nx.DiGraph()
    #    #Add the edges
    #    for ti, lvars in enumerate(op_in_lvars):
    #        op_nid = ln_to_nid[ti]
    #        tmp_vals = [_to_int(sol[lvar.value]) for lvar in lvars]
    #        #Add edge to input
    #        g.add_edge('In', op_nid)
    #        for v, lvar in zip(tmp_vals, lvars):
    #            assert v in lvar_to_nid
    #            g.add_edge(lvar_to_nid[v], op_nid)
    #            int_to_lval[v] = sol[lvar.value]

    #    #Add Output edges
    #    for oval in [_to_int(sol[lvar.value]) for lvar in output_lvars]:
    #        assert oval in lvar_to_nid
    #        g.add_edge(lvar_to_nid[oval], "Out")

    #    for k, lval in int_to_lval.items():
    #        assert _to_int(lval) == k

    #    all_lvars = flat(op_in_lvars) + flat(op_out_lvars) + output_lvars
    #    i_to_lvars = {}
    #    for lvar in all_lvars:
    #        v = int(sol[lvar.value].constant_value())
    #        i_to_lvars.setdefault(v, []).append(lvar)

    #    def sort_to_sol(sort):
    #        v_sols = []
    #        for from_nid, to_nid in zip(nids[1:-1], sort[1:-1]):
    #            for from_val, to_val in zip(from_nid, to_nid):
    #                to_lval = int_to_lval[to_val]
    #                v_sols.append({lvar.value: to_lval for lvar in i_to_lvars[from_val]})

    #        new_sol = dict(sol)
    #        for d in v_sols:
    #            new_sol = {**new_sol, **d}
    #        return new_sol

    #    #Run the gen all topographical orderings algorithm
    #    for sort in nx.all_topological_sorts(g):
    #        new_sol = sort_to_sol(sort)
    #        yield new_sol


    #def gen_op_permutations(self, sol):
    #    input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars

    #    #Get indices of each commutative op
    #    commute_idxs = []
    #    for i, op in enumerate(self.op_list):
    #        if op.comm_info:
    #            commute_idxs.append(i)

    #    lvar_perms = []
    #    lvar_list = []
    #    for i in commute_idxs:
    #        lvar_list += [lvar.value for lvar in op_in_lvars[i]]
    #        lvals = [sol[lvar.value] for lvar in op_in_lvars[i]]
    #        lvar_perms.append(set(it.permutations(lvals)))

    #    for lvals in it.product(*lvar_perms):
    #        lval_list = flat([lval_tuple for lval_tuple in lvals])
    #        new_vals = {lvar: lval for lvar, lval in zip(lvar_list, lval_list)}
    #        new_sol = {**sol, **new_vals}
    #        yield new_sol
    #        #sols.append(new_sol)
    #    #assert sum([int(sol==_sol) for _sol in sols]) == 1, str([int(sol==_sol) for _sol in sols])
    #    #return sols

    def pattern_from_sol(self, sol):
        num_inputs = len(self.iT)
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        if len(hard_const_lvars) > 0:
            raise NotImplementedError()

        op_out_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_out_lvars]
        op_in_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_in_lvars]
        output_lvals = [_to_int(sol[lvar.value]) for lvar in output_lvars]
        synth_vals = [_to_int(sol[var.value]) for var in self.synth_vars]

        lval_to_src = {i:(-1, i) for i in range(num_inputs)}
        for opi, lvals in enumerate(op_out_lvals):
            lval_to_src.update({lval:(opi, i) for i, lval in enumerate(lvals)})

        P = (input_lvars, output_lvals, op_in_lvals, op_out_lvals, synth_vals)
        p = Pattern.init_prog(self.iT, self.oT, self.op_list, P)
        return p


    def match_one_pattern(self, p: Pattern, op_mapping):
        #Interior edges
        interior_edges = []
        dont_care_lvars = {}
        for (li, lai), (ri, rai) in p.interior_edges:
            r_lvar = self.op_in_lvars[op_mapping[ri]][rai]
            if isinstance(p.ops[li].comb, CBVDontCare) or isinstance(p.ops[li].comb, BVDontCare):
                dont_care_lvars.setdefault(li,[]).append(r_lvar)
            else:
                l_lvar = self.op_out_lvars[op_mapping[li]][lai]
                interior_edges.append(l_lvar==r_lvar)
        #Exterior edges
        in_lvars = {}
        for (li, lai), (ri, rai) in p.in_edges:
            assert li == -1
            assert ri != p.num_ops
            r_lvar = self.op_in_lvars[op_mapping[ri]][rai]
            in_lvars.setdefault(lai,[]).append(r_lvar)
        out_lvars = {}
        for (li, lai), (ri, rai) in p.out_edges:
            assert ri == p.num_ops
            assert li != -1
            l_lvar = self.op_out_lvars[op_mapping[li]][lai]
            assert rai not in out_lvars
            out_lvars[rai] = l_lvar
        assert len(out_lvars) == len(self.output_lvars)

        dont_care_conds = []
        for lvars in dont_care_lvars.values():
            for lv0, lv1 in zip(lvars[:-1], lvars[1:]):
                dont_care_conds.append(lv0 == lv1)

        # every input group points to the same src
        in_conds = [fc.And([lv0==lv1 for lv0,lv1 in zip(lvars[:-1], lvars[1:])]) for lvars in in_lvars.values()]

        op_in_mask = self.lvar_t(0)
        input_mask= self.lvar_t(0)
        for l_lvars in in_lvars.values():
            op_in_mask |= (self.lvar_t(1) << l_lvars[0])
        for l_lvar in self.input_lvars:
            input_mask |= (self.lvar_t(1) << l_lvar)
        #we cannot use an equality comparison here because some inputs
        #may be connected to by dont cares
        in_conds.append((op_in_mask & (~input_mask)) == 0)

        op_out_mask = self.lvar_t(0)
        output_mask= self.lvar_t(0)
        for l_lvar in out_lvars.values():
            op_out_mask |= (self.lvar_t(1) << l_lvar)
        for l_lvar in self.output_lvars:
            output_mask |= (self.lvar_t(1) << l_lvar)
        out_conds = [op_out_mask == output_mask]

        assert len(self.synth_vars) == len(p.synth_vals)
        synth_conds = [var == val for var, val in zip(self.synth_vars, p.synth_vals)]
        return fc.And(in_conds + interior_edges + out_conds + synth_conds + dont_care_conds)

    def match_rule_dag(self, dag, r_matches):
        l_insides = [m[0] for m in r_matches]
        l_ins = [m[1] for m in r_matches]
        l_outs = [m[2] for m in r_matches]
        ios = []
        for d in dag:
            (src, src_i), (snk, snk_i) = d
            if src==-1:
                l_src_lvar = src_i
            else:
                l_src_lvar = l_outs[src][src_i]
            if snk == len(r_matches):
                l_snk_lvar = self.output_lvars[snk_i]
            else:
                l_snk_lvar = l_ins[snk][snk_i]
            ios.append(l_src_lvar == l_snk_lvar)
        return fc.And([fc.And(l_insides), fc.And(ios)])

    #Will yield all matches of the single pattern
    def match_all_patterns(self, pat: Pattern):
        pat_ops = _list_to_dict(pat.op_names)
        cs_ops = _list_to_dict([op.qualified_name for op in self.op_list])
        ops = list(pat_ops.keys())
        assert set(ops).issubset(set(cs_ops.keys()))
        poss = [it.permutations(cs_ops[op], len(pat_ops[op])) for op in ops]
        for cs_op_ids in it.product(*poss):
            assert len(cs_op_ids) == len(ops)
            for p in pat.enum_all_equal():
                maps = [{pid:csid for pid,csid in zip(p.op_dict[op],ids)} for op, ids in zip(ops, cs_op_ids)]
                pid_to_csid = functools.reduce(lambda d0, d1: {**d0, **d1}, maps)
                yield self.match_one_pattern(p, pid_to_csid)


            #pc_ids = [{pi:ci for pi, ci in zip(pat_ops[op],ids)} for op, ids in zip(ops, cs_op_ids)]
            #pid_to_csid = functools.reduce(lambda x,y: {**x,**y}, pc_ids)
            #yield self.match_one_pattern(pat, pid_to_csid)

    #Returns a formula that is true when the pattern matches at least once
    def any_pat_match(self, pat: Pattern):
        return fc.Or([cond for cond,_,_ in self.match_all_patterns(pat)])




    #@property
    #def P_sym_same_op(self):
    #    assert self.sym_opts.same_op
    #    #Tactic: Same as the input_perm tactic

    #    #For each op kind
    #    ops = _list_to_dict([op.qualified_name for op in self.op_list])
    #    P_same_op = []
    #    for op_name, op_ids in ops.items():
    #        if len(op_ids) == 1:
    #            continue

    #        op = self.op_list[op_ids[0]]
    #        op_iT, op_oT = op.get_type()
    #        if len(op_oT) > 1:
    #            raise NotImplementedError()
    #        n = type_to_nT(op_oT[0])
    #        snks = sorted(self.snk_n[n].keys())
    #        op_snks = []
    #        for opi in op_ids:
    #            op_snks += [snk for snk in snks if snk[0]==opi]
    #        snks = op_snks + [snk for snk in snks if snk not in op_snks]
    #        self.op_to_sorted_snks[op_name] = snks
    #        ens = [] #ens[opi][snk]
    #        for opi in op_ids:
    #            src_lvar = self.op_out_lvars[opi][0]
    #            lvars = {snk:self.snk_n[n][snk].lvar==src_lvar for snk in snks}
    #            ens.append(lvars)

    #        conds = []
    #        used = [ht.SMTBit(0) for _ in op_ids]
    #        for snk in snks:
    #            lvars = [ens[opi][snk] for opi in range(len(op_ids))]
    #            op_conds = []
    #            for ui, u in enumerate(used[:-1]):
    #                op_conds.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
    #            used = [u | lvars[ui] for ui, u in enumerate(used)]
    #            conds.append(fc.And(op_conds))
    #        P_same_op.append(fc.And(conds))
    #    ret = fc.And(P_same_op)
    #    return ret


    def comb_from_solved(self, lvals, name: QSym = QSym("Default", "P")):
       spec_iTs, spec_oTs = self.iT, self.oT 

       input_vars, hard_consts, output_vars, op_out_vars, op_in_vars = self.vars
       input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
       num_inputs = len(spec_iTs)
       #Fill in all the lvars
       output_lvars = [_to_int(lvals[lvar.value]) for lvar in output_lvars]
       def name_from_loc(loc, src=None):
           if loc < num_inputs:
               return Sym(f"I{loc}")
           elif loc < num_inputs + len(hard_consts):
               assert src is not None
               i, j = src
               iT = self.op_list[i].get_type()[0][j].type
               if isinstance(iT, TypeCall):
                   assert isinstance(iT.type, BVType)
                   N = iT.pargs[0].value
                   const_val = hard_consts[loc - num_inputs]
                   return make_bv_const(N, const_val)
               else:
                   raise NotImplementedError()
           else:
               loc = loc - (num_inputs + len(hard_consts))
               return Sym(f"t{loc}")

       out_lvar_vals = {}
       in_lvar_vals = {}
       for i in range(len(op_out_lvars)):
           out_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_out_lvars[i]]
           in_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_in_lvars[i]]

       inputs = [InDecl(name_from_loc(i), nT_to_type(T)) for i, T in enumerate(spec_iTs)]
       outputs = [OutDecl(name_from_loc(output_lvars[i]), nT_to_type(T)) for i, T in enumerate(spec_oTs)]
       stmts = []
       for i, out_lvars in sorted(out_lvar_vals.items(), key=lambda item: item[1][0]):
           lhss = [name_from_loc(loc) for loc in out_lvars]
           op = self.op_list[i]
           args = [name_from_loc(loc, src=(i,j)) for j, loc in enumerate(in_lvar_vals[i])]
           stmts.append(AssignStmt(lhss, [op.call_expr([], args)]))
       comb = CombProgram(name, [*inputs, *outputs, *stmts])
       return comb