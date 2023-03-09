import collections
import itertools as it
import typing as tp
from dataclasses import dataclass

import hwtypes as ht
import networkx as nx
from hwtypes import smt_utils as fc

from . import Comb
from .ast import Type, QSym, Sym, TypeCall, BVType, InDecl, OutDecl
from .ir import _make_list, AssignStmt, CombProgram
from .stdlib import make_bv_const
from .synth import PatternSynth, get_var, SBV, Pattern
from .utils import flat, _to_int


class CombSynth(PatternSynth):
    def __init__(self, *args):
        super().__init__(*args)

        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")
        iTs, oTs = self.comb_type

        # Structure
        input_vars = [get_var(f"{self.prefix}_V_In{i}", T) for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        #const_vars = []
        output_vars = [get_var(f"{self.prefix}_V_Out{i}", T) for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        tot_locs = Ninputs + Nconsts
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{self.prefix}_V_Op[{opi}]_in[{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{self.prefix}_V_Op[{opi}]_out[{i}]", T) for i, T in enumerate(op_oTs)])
            tot_locs += op.num_outputs
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)
        self.tot_locs = tot_locs
        lvar_t_width = tot_locs
        lvar_t = SBV[lvar_t_width]

        #These can be hardcoded
        input_lvars = list(range(len(input_vars)))
        Ninputs = len(input_vars)
        hard_const_lvars = list(range(Ninputs, Ninputs +len(hard_consts)))
        op_out_lvars = []
        op_in_lvars = []
        for opi, op in enumerate(self.op_list):
            op_iTs, op_oTs = op.get_type()
            op_in_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_in[{i}]", lvar_t_width) for i, T in enumerate(op_iTs)])
            op_out_lvars.append([get_var(f"{self.prefix}_L_op[{opi}]_out[{i}]", lvar_t_width) for i, T in enumerate(op_oTs)])
        output_lvars = [get_var(f"{self.prefix}_L_out[{i}]", lvar_t_width) for i in range(len(output_vars))]
        self.op_in_lvars = op_in_lvars
        self.op_out_lvars = op_out_lvars
        self.output_lvars = output_lvars

        #get list of lvars (existentially quantified in final query)
        self.E_vars = output_lvars + flat(op_out_lvars) + flat(op_in_lvars)
        self.lvars = (input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars)

        self.rhs_lvars = flat(op_in_lvars) + output_lvars

        And = fc.And
        #Lib Spec (P_lib)
        #   temp_var[i] = OP(*op_in_vars[i])
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(op_out_vars[i][j] == op_out_var)


        #Well formed program (P_wfp)
        flat_op_out_lvars = flat(op_out_lvars)

        # Temp locs and output locs are in range of temps
        P_in_range = []
        for lvar in flat_op_out_lvars:
            P_in_range.append(And([lvar>=Ninputs+Nconsts, lvar < tot_locs]))

        #op in locs and outputs are in range(0,tot)

        for lvar in self.rhs_lvars:
            P_in_range.append(lvar < tot_locs)

        #Ints are >= 0
        #BitVectors do not need this check
        if lvar_t is ht.SMTInt:
            for lvars in (
                    output_lvars,
                    flat(op_out_lvars),
                    flat(op_in_lvars),
            ):
                for lvar in lvars:
                    assert isinstance(lvar, lvar_t)
                    P_in_range.append(lvar >= 0)

        #TODO flag?
        #output loc cannot be inputs
        #for lvar in output_lvars:
        #    P_in_range.append(lvar >= Ninputs+Nconsts)

        # Temp locs are unique
        #Could simplify to only the first lhs of each stmt
        P_loc_unique = []
        for i in range(len(flat_op_out_lvars)):
            for j in range(i+1, len(flat_op_out_lvars)):
                P_loc_unique.append(flat_op_out_lvars[i] != flat_op_out_lvars[j])

        # multi outputs are off by 1
        P_multi_out = []
        for lvars in op_out_lvars:
            for lv0, lv1 in zip(lvars, lvars[1:]):
                P_multi_out.append(lv0+1==lv1)

        P_acyc = []
        # ACYC Constraint
        #  op_out_lvars[i] > op_in_lvars[i]
        for o_lvars, i_lvars in zip(op_out_lvars, op_in_lvars):
            P_acyc += [o_lvars[0] > ilvar for ilvar in i_lvars]

        #Same operations have a strict order
        op_to_i = {}
        for i, op in enumerate(self.op_list):
            op_to_i.setdefault(op.qualified_name, []).append(i)

        P_same_op = []
        for op, ilist in op_to_i.items():
            if len(ilist) > 1:
                for i, j in zip(ilist[:-1], ilist[1:]):
                    assert i < j
                    P_same_op.append(op_out_lvars[i][0] < op_out_lvars[j][0])

        #Strict ordering on arguments of commutative ops
        P_comm = []
        #TODO Re-enable
        for i, op in enumerate(self.op_list):
            if op.commutative:
                for lv0, lv1 in  zip(op_in_lvars[i][:-1], op_in_lvars[i][1:]):
                    P_comm.append(lv0 <= lv1)

        def rhss():
            for lvar in flat(op_in_lvars):
                yield lvar
            for lvar in output_lvars:
                yield lvar

        #All vars are used
        used = lvar_t(0)
        for lvar_rhs in rhss():
            used |= (lvar_t(1) << lvar_rhs)
        P_used = (used == (2**tot_locs)-1)

        P_wfp = [
            And(P_in_range),
            And(P_loc_unique),
            And(P_multi_out),
            And(P_acyc),
            And(P_same_op),
            And(P_comm),
            P_used,
        ]

        #Locations correspond to vars (P_conn)
        # (Lx == Ly) => (X==Y)
        pairs = []
        for lvars, vars in (
            (input_lvars, input_vars),
            (output_lvars, output_vars),
            (hard_const_lvars, hard_consts),
            (flat(op_out_lvars), flat(op_out_vars)),
            (flat(op_in_lvars), flat(op_in_vars)),
        ):
            for lvar, var in zip(lvars, vars):
                pairs.append((lvar, var))
        P_conn = []
        for i in range(len(pairs)):
            for j in range(i+1, len(pairs)):
                lv0, v0 = pairs[i]
                lv1, v1 = pairs[j]
                #Types need to match
                #Type is allowed to be an int
                if type(v0) != type(v1) and not isinstance(v0, int) and  not isinstance(v1, int):
                    continue
                #skip if both loc vars are int
                if isinstance(lv0, int) and isinstance(lv1, int):
                    continue
                P_conn.append(fc.Implies(lv0==lv1, v0==v1))

        self.P_wfp = And(P_wfp)
        self.P_lib = And(P_lib)
        self.P_conn = And(P_conn)


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

    #Makes sure the typing makes sense for the query
    def types_viable(self):
        def cnt_vals(vals):
            cnt = collections.defaultdict(int)
            for v in vals:
                cnt[v] += 1
            return cnt

        spec_iTs, spec_oTs = self.comb_type
        spec_inputs = cnt_vals(i.type for i in spec_iTs)
        spec_outputs = cnt_vals(o.type for o in spec_oTs)

        op_inputs = cnt_vals(flat([[i.type for i in op.get_type()[0]] for op in self.op_list]))
        op_outputs = cnt_vals(flat([[o.type for o in op.get_type()[1]] for op in self.op_list]))

        if not all(t in op_inputs and op_inputs[t] >= cnt for t, cnt in spec_inputs.items()):
            return False
        if not all(t in op_outputs and op_outputs[t] >= cnt for t, cnt in spec_outputs.items()):
            return False
        return True

    def pattern_from_solved(self, sol):
        spec_iTs, spec_oTs = self.comb_type
        num_inputs = len(spec_iTs)
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        if len(hard_const_lvars) > 0:
            raise NotImplementedError()
        op_out_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_out_lvars]
        op_in_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_in_lvars]
        output_lvals = [_to_int(sol[lvar.value]) for lvar in output_lvars]
        nodes = [(op_out_lvals[i][0], i) for i, _ in enumerate(self.op_list)]
        #ni is new sorted index
        #i is original index
        i_to_ni = {i:ni for ni, (_,i) in enumerate(sorted(nodes))}
        ni_to_i = {ni:i for ni, (_,i) in enumerate(sorted(nodes))}

        lval_to_node = {}
        for i in range(num_inputs):
            lval_to_node[i] = ("In", i)
        for i, lvals in enumerate(op_out_lvals):
            for argi, lval in enumerate(lvals):
                assert lval not in lval_to_node
                lval_to_node[lval] = (i_to_ni[i], argi)

        sorted_ops = [self.op_list[i] for ni, i in ni_to_i.items()]
        p = Pattern(self.comb_type, sorted_ops)
        for opi, lvals in enumerate(op_in_lvals):
            for argi, lval in enumerate(lvals):
                rhs = (i_to_ni[opi], argi)
                lhs = lval_to_node[lval]
                p.add_edge(lhs, rhs)
        for out_i, lval in enumerate(output_lvals):
            rhs = ("Out", out_i)
            lhs = lval_to_node[lval]
            p.add_edge(lhs, rhs)
        return p


    def comb_from_solved(self, lvals, name: QSym):
        spec_iTs, spec_oTs = self.comb_type

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

        inputs = [InDecl(name_from_loc(i), T) for i, T in enumerate(spec_iTs)]
        outputs = [OutDecl(name_from_loc(output_lvars[i]), T) for i, T in enumerate(spec_oTs)]
        stmts = []
        for i, out_lvars in sorted(out_lvar_vals.items(), key=lambda item: item[1][0]):
            lhss = [name_from_loc(loc) for loc in out_lvars]
            op = self.op_list[i]
            args = [name_from_loc(loc, src=(i,j)) for j, loc in enumerate(in_lvar_vals[i])]
            stmts.append(AssignStmt(lhss, [op.call_expr([], args)]))
        comb = CombProgram(name, [*inputs, *outputs, *stmts])
        return comb