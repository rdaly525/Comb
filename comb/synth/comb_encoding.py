import collections
import itertools as it

from hwtypes import SMTBitVector as SBV
import networkx as nx
from hwtypes import smt_utils as fc
import hwtypes as ht
from ..frontend.ast import QSym, Sym, TypeCall, BVType, InDecl, OutDecl
from ..frontend.ir import AssignStmt, CombProgram
from ..frontend.stdlib import make_bv_const
from .pattern import PatternEncoding, Pattern
from .solver_utils import get_var
from .utils import flat, _to_int, _list_to_dict, type_to_N
from hwtypes import SMTBitVector as SBV

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
        for opi, op in enumerate(self.op_list):
            op_iTs, op_oTs = op.get_type()
            op_in_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_in[{i}]", lvar_t_width) for i, T in enumerate(op_iTs)])
            op_out_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_out[{i}]", lvar_t_width) for i, T in enumerate(op_oTs)])
        output_lvars = [get_var(f"{self.prefix}_L_out[{i}]", lvar_t_width) for i in range(len(self.output_vars))]
        self.op_in_lvars = op_in_lvars
        self.op_out_lvars = op_out_lvars
        self.output_lvars = output_lvars

        #get list of lvars (existentially quantified in final query)
        self.E_vars = output_lvars + flat(op_out_lvars) + flat(op_in_lvars)
        self.lvars = (self.input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars)
        self.rhs_lvars = flat(op_in_lvars) + output_lvars
        self.Ninputs = Ninputs
        self.Nconsts = 0
        self.tot_locs = tot_locs

        self.src_n = {n: {(-1,id):(self.input_lvars[id], self.input_vars[id]) for id in ids} for n, ids in _list_to_dict(self.iT).items()}
        self.snk_n = {n: {(self.num_ops,id):(self.output_lvars[id], self.output_vars[id]) for id in ids} for n, ids in _list_to_dict(self.oT).items()}
        for opi, op in enumerate(self.op_list):
            iT, oT = op.get_type()
            iT = [type_to_N(t) for t in iT]
            oT = [type_to_N(t) for t in oT]
            for n, ids in _list_to_dict(iT).items():
                self.snk_n.setdefault(n, {}).update({(opi, id):(self.op_in_lvars[opi][id], self.op_in_vars[opi][id]) for id in ids})
            for n, ids in _list_to_dict(oT).items():
                self.src_n.setdefault(n, {}).update({(opi, id):(self.op_out_lvars[opi][id], self.op_out_vars[opi][id]) for id in ids})





    @property
    def P_conn(self):
        P_conn = []
        for n, src_dict in self.src_n.items():
            assert n in self.snk_n
            snk_dict = self.snk_n[n]
            for (src_lvar, src_var), (snk_lvar, snk_var) in it.product(src_dict.values(), snk_dict.values()):
                P_conn.append(fc.Implies(src_lvar==snk_lvar, src_var==snk_var))
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
        return fc.And(P_in_range)


        #TODO flag?
        #output loc cannot be inputs
        #for lvar in output_lvars:
        #    P_in_range.append(lvar >= Ninputs+Nconsts)

    @property
    def P_loc_unique(self):
        # Temp locs are unique
        #Could simplify to only the first lhs of each stmt
        out_lvars = [lvars[0] for lvars in self.op_out_lvars]
        P_loc_unique = []
        for lvar_a, lvar_b in it.combinations(out_lvars, 2):
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
            P_acyc += [o_lvars[0] > ilvar for ilvar in i_lvars]
        return fc.And(P_acyc)

    @property
    def P_used_source(self):
        def rhss():
            for lvar in flat(self.op_in_lvars):
                yield lvar
            for lvar in self.output_lvars:
                yield lvar

        #All vars are used
        used = self.lvar_t(0)
        for lvar_rhs in rhss():
            used |= (self.lvar_t(1) << lvar_rhs)
        P_used = (used == (2**self.tot_locs)-1)
        return P_used

    @property
    def P_sym_same_op(self):
        #Same operations have a strict order
        op_to_i = _list_to_dict([op.qualified_name for op in self.op_list])

        #Does not work I think. Try to code up the example. (not(not(x)) + not(not(x)) or something like that
        # This can have arbitrary interleavings of nots while still obeying
        #raise NotImplementedError()
        P_same_op = []
        for op, ilist in op_to_i.items():
            if len(ilist) > 1:
                for i, j in zip(ilist[:-1], ilist[1:]):
                    assert i < j
                    P_same_op.append(self.op_out_lvars[i][0] < self.op_out_lvars[j][0])
        return fc.And(P_same_op)

    @property
    def P_sym_comm(self):
        #Strict ordering on arguments of commutative ops
        P_comm = []
        for i, op in enumerate(self.op_list):
            if op.commutative:
                for lv0, lv1 in  zip(self.op_in_lvars[i][:-1], self.op_in_lvars[i][1:]):
                    P_comm.append(lv0 <= lv1)
        return fc.And(P_comm)

    @property
    def P_sym_input_perm(self):
        assert self.sym_opts.input_perm
        input_T = _list_to_dict(self.iT)

        # Create a set of all sources/snks sorted by type
        P_perms = []
        for n, ids in input_T.items():
            snk_dict = self.snk_n[n]
            src_dict = self.src_n[n]
            snks = sorted(snk_dict.keys())
            P_perm = []
            used = [ht.SMTBit(0) for _ in ids]
            for snk in snks:
                snk_lvar = snk_dict[snk][0]
                lvars = [snk_lvar == src_dict[(-1, id)][0] for id in ids]
                i_perm = []
                for ui, u in enumerate(used[:-1]):
                    i_perm.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
                used = [u | lvars[ui] for ui, u in enumerate(used)]
                P_perm.append(fc.And(i_perm))
            P_perms.append(fc.And(P_perm))
        ret = fc.And(P_perms)
        return ret

    @property
    def P_wfp(self):
        P_wfp = [
            self.P_in_range,
            self.P_loc_unique,
            self.P_multi_out,
            self.P_acyc,
            self.P_used_source,
        ]
        return fc.And(P_wfp)

    def fix_comm(self, sol):
        comm_ids = [i for i, op in enumerate(self.op_list) if op.commutative]
        v_sols = []
        for i in comm_ids:
            lvars = self.op_in_lvars[i]
            lvals = [sol[lvar.value] for lvar in lvars]
            vals = sorted([(int(sol[lvar.value].constant_value()), li) for li, lvar in enumerate(lvars)])
            v_sols.append({lvars[si].value: lvals[oi] for si, (v, oi) in enumerate(vals)})

        new_sol = dict(sol)
        for d in v_sols:
            new_sol = {**new_sol, **d}
        return new_sol


    def gen_all_program_orders(self, sol):
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        #Create Graph from sol
        lvar_to_nid = {}
        int_to_lval = {}
        for v in input_lvars:
            lvar_to_nid[v] = 'In'
        assert len(hard_const_lvars) == 0
        ln_to_nid = {}

        nids = []
        for li, lvars in enumerate(op_out_lvars):
            tmp_vals = tuple(_to_int(sol[lvar.value]) for lvar in lvars)
            nid = tmp_vals
            nids.append((tmp_vals[0], nid))
            ln_to_nid[li] = nid
            for v, lvar in zip(tmp_vals, lvars):
                lvar_to_nid[v] = nid
                int_to_lval[v] = sol[lvar.value]
        nids = ["In"] + [v for _, v in sorted(nids)] + ["Out"]
        g = nx.DiGraph()
        #Add the edges
        for ti, lvars in enumerate(op_in_lvars):
            op_nid = ln_to_nid[ti]
            tmp_vals = [_to_int(sol[lvar.value]) for lvar in lvars]
            #Add edge to input
            g.add_edge('In', op_nid)
            for v, lvar in zip(tmp_vals, lvars):
                assert v in lvar_to_nid
                g.add_edge(lvar_to_nid[v], op_nid)
                int_to_lval[v] = sol[lvar.value]

        #Add Output edges
        for oval in [_to_int(sol[lvar.value]) for lvar in output_lvars]:
            assert oval in lvar_to_nid
            g.add_edge(lvar_to_nid[oval], "Out")

        for k, lval in int_to_lval.items():
            assert _to_int(lval) == k

        all_lvars = flat(op_in_lvars) + flat(op_out_lvars) + output_lvars
        i_to_lvars = {}
        for lvar in all_lvars:
            v = int(sol[lvar.value].constant_value())
            i_to_lvars.setdefault(v, []).append(lvar)

        def sort_to_sol(sort):
            v_sols = []
            for from_nid, to_nid in zip(nids[1:-1], sort[1:-1]):
                for from_val, to_val in zip(from_nid, to_nid):
                    to_lval = int_to_lval[to_val]
                    v_sols.append({lvar.value: to_lval for lvar in i_to_lvars[from_val]})

            new_sol = dict(sol)
            for d in v_sols:
                new_sol = {**new_sol, **d}
            return new_sol

        #Run the gen all topographical orderings algorithm
        for sort in nx.all_topological_sorts(g):
            new_sol = sort_to_sol(sort)
            yield new_sol


    def gen_op_permutations(self, sol):
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars

        #Get indices of each commutative op
        commute_idxs = []
        for i, op in enumerate(self.op_list):
            if op.commutative:
                commute_idxs.append(i)

        lvar_perms = []
        lvar_list = []
        for i in commute_idxs:
            lvar_list += [lvar.value for lvar in op_in_lvars[i]]
            lvals = [sol[lvar.value] for lvar in op_in_lvars[i]]
            lvar_perms.append(set(it.permutations(lvals)))

        for lvals in it.product(*lvar_perms):
            lval_list = flat([lval_tuple for lval_tuple in lvals])
            new_vals = {lvar: lval for lvar, lval in zip(lvar_list, lval_list)}
            new_sol = {**sol, **new_vals}
            yield new_sol
            #sols.append(new_sol)
        #assert sum([int(sol==_sol) for _sol in sols]) == 1, str([int(sol==_sol) for _sol in sols])
        #return sols

    def pattern_from_sol(self, sol):
        num_inputs = len(self.iT)
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        if len(hard_const_lvars) > 0:
            raise NotImplementedError()

        op_out_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_out_lvars]
        op_in_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_in_lvars]
        output_lvals = [_to_int(sol[lvar.value]) for lvar in output_lvars]

        lval_to_src = {i:(-1, i) for i in range(num_inputs)}
        for opi, lvals in enumerate(op_out_lvals):
            lval_to_src.update({lval:(opi, i) for i, lval in enumerate(lvals)})

        p = Pattern(self.iT, self.oT, self.op_list)
        for opi, lvals in enumerate(op_in_lvals):
            for i, lval in enumerate(lvals):
                src = lval_to_src[lval]
                p.add_edge(src, (opi, i))
        for i, lval in enumerate(output_lvals):
            src = lval_to_src[lval]
            p.add_edge(src, (self.num_ops, i))
        return p


    #def comb_from_solved(self, lvals, name: QSym):
    #    spec_iTs, spec_oTs = self.comb_type

    #    input_vars, hard_consts, output_vars, op_out_vars, op_in_vars = self.vars
    #    input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
    #    num_inputs = len(spec_iTs)
    #    #Fill in all the lvars
    #    output_lvars = [_to_int(lvals[lvar.value]) for lvar in output_lvars]
    #    def name_from_loc(loc, src=None):
    #        if loc < num_inputs:
    #            return Sym(f"I{loc}")
    #        elif loc < num_inputs + len(hard_consts):
    #            assert src is not None
    #            i, j = src
    #            iT = self.op_list[i].get_type()[0][j].type
    #            if isinstance(iT, TypeCall):
    #                assert isinstance(iT.type, BVType)
    #                N = iT.pargs[0].value
    #                const_val = hard_consts[loc - num_inputs]
    #                return make_bv_const(N, const_val)
    #            else:
    #                raise NotImplementedError()
    #        else:
    #            loc = loc - (num_inputs + len(hard_consts))
    #            return Sym(f"t{loc}")

    #    out_lvar_vals = {}
    #    in_lvar_vals = {}
    #    for i in range(len(op_out_lvars)):
    #        out_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_out_lvars[i]]
    #        in_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_in_lvars[i]]

    #    inputs = [InDecl(name_from_loc(i), T) for i, T in enumerate(spec_iTs)]
    #    outputs = [OutDecl(name_from_loc(output_lvars[i]), T) for i, T in enumerate(spec_oTs)]
    #    stmts = []
    #    for i, out_lvars in sorted(out_lvar_vals.items(), key=lambda item: item[1][0]):
    #        lhss = [name_from_loc(loc) for loc in out_lvars]
    #        op = self.op_list[i]
    #        args = [name_from_loc(loc, src=(i,j)) for j, loc in enumerate(in_lvar_vals[i])]
    #        stmts.append(AssignStmt(lhss, [op.call_expr([], args)]))
    #    comb = CombProgram(name, [*inputs, *outputs, *stmts])
    #    return comb