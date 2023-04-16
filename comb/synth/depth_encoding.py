import collections
import itertools as it

from hwtypes import SMTBitVector as SBV
from hwtypes import smt_utils as fc
import hwtypes as ht
from ..frontend.ast import QSym, Sym, TypeCall, BVType, InDecl, OutDecl
from ..frontend.ir import AssignStmt, CombProgram
from ..frontend.stdlib import make_bv_const
from .pattern import PatternEncoding, Pattern
from .solver_utils import get_var
from .utils import flat, _to_int, _list_to_dict, type_to_nT, types_to_nTs
from hwtypes import SMTBitVector as SBV
from collections import namedtuple

Lvar = namedtuple('Lvar', 'd, id')
VarPair = namedtuple('VarPair', 'lvar, var')

#Caleb encoding
class DepthEncoding(PatternEncoding):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        #hard_consts = []

        tot_ids = len(self.iT) + sum([len(ovs) for ovs in self.op_out_vars])
        lvar_t_width = tot_ids
        self.lvar_t = SBV[lvar_t_width]
        def _get_var(name):
            return get_var(name, lvar_t_width)
        src_lvars = {-1:[Lvar(d=0,id=id) for id in range(len(self.iT))]}
        snk_lvars = {}
        id_to_src = {i:(-1, i) for i in range(len(self.iT))}
        id = len(self.iT)
        E_vars = []
        for opi, op in enumerate(self.op_list):
            iT, oT = op.get_type()
            iT = [type_to_nT(T) for T in iT]
            in_lvars = []
            for i, n in enumerate(iT):
                in_id = _get_var(f"{self.prefix}_id_OpIn[{opi}][{i}]")
                in_d = _get_var(f"{self.prefix}_D_OpIn[{opi}][{i}]")
                E_vars.extend([in_id, in_d])
                in_lvars.append(Lvar(d=in_d, id=in_id))
            snk_lvars[opi] = in_lvars

            out_d = _get_var(f"{self.prefix}_D_OpOut[{opi}]")
            E_vars.extend([out_d])
            out_lvars = []
            for i in range(len(oT)):
                out_lvars.append(Lvar(d=out_d, id=id))
                id_to_src[id]=(opi, i)
                id += 1
            src_lvars[opi] = out_lvars
        output_lvars = []
        for i, n in enumerate(self.oT):
            out_id = _get_var(f"{self.prefix}_id_Out[{i}]")
            out_d = _get_var(f"{self.prefix}_D_Out[{i}]")
            E_vars.extend([out_id, out_d])
            output_lvars.append(Lvar(d=out_d, id=out_id))
        snk_lvars[self.num_ops] = output_lvars

        self.src_lvars = src_lvars
        self.snk_lvars = snk_lvars
        self.id_to_src = id_to_src
        self.E_vars = E_vars
        self.tot_ids = tot_ids

        self.op_to_sorted_snks = {} #Used to save the symmetry orderings
        self.src_n = {n: {(-1, id):VarPair(src_lvars[-1][id], self.input_vars[id]) for id in ids} for n, ids in _list_to_dict(self.iT).items()}
        self.snk_n = {n: {(self.num_ops,id):VarPair(snk_lvars[self.num_ops][id], self.output_vars[id]) for id in ids} for n, ids in _list_to_dict(self.oT).items()}
        for opi, op in enumerate(self.op_list):
            iT, oT = op.get_type()
            iT = [type_to_nT(t) for t in iT]
            oT = [type_to_nT(t) for t in oT]
            for n, ids in _list_to_dict(iT).items():
                self.snk_n.setdefault(n, {}).update({(opi, id):VarPair(snk_lvars[opi][id], self.op_in_vars[opi][id]) for id in ids})
            for n, ids in _list_to_dict(oT).items():
                self.src_n.setdefault(n, {}).update({(opi, id):VarPair(src_lvars[opi][id], self.op_out_vars[opi][id]) for id in ids})

    @property
    def P_conn(self):
        P_conn = []
        for n, src_dict in self.src_n.items():
            assert n in self.snk_n
            snk_dict = self.snk_n[n]
            for src_v, snk_v in it.product(src_dict.values(), snk_dict.values()):
                P_conn.append(fc.Implies(src_v.lvar.id == snk_v.lvar.id, src_v.var==snk_v.var))
        return fc.And(P_conn)

    @property
    def P_acyc(self):
        P_acyc = []
        # ACYC Constraint
        #  Depth of inputs must be less than depth of output
        for opi in range(self.num_ops):
            o_lvars, i_lvars = self.src_lvars[opi], self.snk_lvars[opi]
            o_d = o_lvars[0].d
            P_acyc.append(fc.And([o_d > i_lvar.d for i_lvar in i_lvars]))
        return fc.And(P_acyc)

    @property
    def P_depth_conn(self):
        P_depth_conn = []
        # ids being equal imply depths are equal
        for n, src_dict in self.src_n.items():
            assert n in self.snk_n
            snk_dict = self.snk_n[n]
            for src_v, snk_v in it.product(src_dict.values(), snk_dict.values()):
                P_depth_conn.append(fc.Implies(src_v.lvar.id == snk_v.lvar.id, src_v.lvar.d==snk_v.lvar.d))
        return fc.And(P_depth_conn)

    @property
    def P_depth_max(self):
        P_depth = []
        # max(depth of inputs) +1 = output depth
        def _max(*vals):
            assert len(vals) > 0
            if len(vals)==1:
                return vals[0]
            mval = _max(*vals[1:])
            return (mval > vals[0]).ite(mval, vals[0])
        for opi in range(self.num_ops):
            o_lvars, i_lvars = self.src_lvars[opi], self.snk_lvars[opi]
            P_depth.append(_max(*[lvar.d for lvar in i_lvars]) + 1==o_lvars[0].d)
        return fc.And(P_depth)

    @property
    def P_used_source(self):
        def get_ids():
            for opi, lvars in self.snk_lvars.items():
                for lvar in lvars:
                    yield lvar.id

        #All vars are used
        used = self.lvar_t(0)
        for id in get_ids():
            used |= (self.lvar_t(1) << id)
        P_used = (used == (2 ** self.tot_ids) - 1)
        return P_used

    @property
    def P_wfp(self):
        P_wfp = [
            self.P_acyc,
            self.P_depth_conn,
            self.P_depth_max,
            self.P_used_source,
            self.P_cse,
        ]
        ret = fc.And(P_wfp)
        #print(ret.serialize())
        return ret

    @property
    def P_sym_comm(self):
        assert self.sym_opts.comm
        raise NotImplementedError()
        #Strict ordering on arguments of commutative ops
        P_comm = []
        for opi, op in enumerate(self.op_list):
            if op.comm_info:
                for lv0, lv1 in zip(self.snk_lvars[opi][:-1], self.snk_lvars[opi][1:]):
                    P_comm.append(lv0.id <= lv1.id)
        return fc.And(P_comm)

    @property
    def P_sym_same_op(self):
        assert self.sym_opts.same_op
        #Tactic: Same as the input_perm tactic

        #For each op kind
        ops = _list_to_dict([op.qualified_name for op in self.op_list])
        P_same_op = []
        for op_name, op_ids in ops.items():
            if len(op_ids) == 1:
                continue

            op = self.op_list[op_ids[0]]
            op_iT, op_oT = op.get_type()
            if len(op_oT) > 1:
                raise NotImplementedError()
            n = type_to_nT(op_oT[0])
            snks = sorted(self.snk_n[n].keys())
            op_snks = []
            for opi in op_ids:
                op_snks += [snk for snk in snks if snk[0]==opi]
            snks = op_snks + [snk for snk in snks if snk not in op_snks]
            self.op_to_sorted_snks[op_name] = snks
            ens = [] #ens[opi][snk]
            for opi in op_ids:
                src_lvar = self.src_lvars[opi][0]
                lvars = {snk:self.snk_n[n][snk].lvar.id==src_lvar.id for snk in snks}
                ens.append(lvars)

            conds = []
            used = [ht.SMTBit(0) for _ in op_ids]
            for snk in snks:
                lvars = [ens[opi][snk] for opi in range(len(op_ids))]
                op_conds = []
                for ui, u in enumerate(used[:-1]):
                    op_conds.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
                used = [u | lvars[ui] for ui, u in enumerate(used)]
                conds.append(fc.And(op_conds))
            P_same_op.append(fc.And(conds))
        ret = fc.And(P_same_op)
        return ret

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
            self.op_to_sorted_snks['In'] = snks
            P_perm = []
            used = [ht.SMTBit(0) for _ in ids]
            for snk in snks:
                snk_lvar = snk_dict[snk].lvar
                lvars = [snk_lvar.id==src_dict[(-1, id)].lvar.id for id in ids]
                i_perm = []
                for ui, u in enumerate(used[:-1]):
                    i_perm.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
                used = [u | lvars[ui] for ui, u in enumerate(used)]
                P_perm.append(fc.And(i_perm))
            P_perms.append(fc.And(P_perm))
        ret = fc.And(P_perms)
        return ret

    def pattern_from_sol(self, sol):
        p = Pattern(self.iT, self.oT, self.op_list)
        for opi in range(self.num_ops+1):
            in_lvars = self.snk_lvars[opi]
            ids = [_to_int(sol[lvar.id.value]) for lvar in in_lvars]
            for snki, id in enumerate(ids):
                assert id in self.id_to_src
                src = self.id_to_src[id]
                snk = (opi, snki)
                p.add_edge(src, snk)

        return p