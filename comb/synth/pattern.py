import hwtypes.smt_utils as fc
from dataclasses import dataclass
from ..frontend.ast import Comb, Type
import typing as tp

from .solver_utils import get_var
from .utils import _make_list

#Represnts the raw dag structure of a particular pattern
class Pattern:
    def __init__(self, comb_type, ops):
        self.comb_type = comb_type
        self.ops = ops
        self.op_names = [op.qualified_name for op in self.ops]
        self.nodes = ['In'] + list(range(len(ops))) + ['Out']
        self.edges = []

    def add_edge(self, lhs, rhs):
        assert len(lhs)==2 and len(rhs)==2
        assert lhs[0] in self.nodes
        assert rhs[0] in self.nodes
        if lhs[0] == "In":
            assert lhs[1] < len(self.comb_type[0])
        if rhs[0] == "Out":
            assert rhs[1] < len(self.comb_type[1])
        self.edges.append((lhs, rhs))

    @property
    def interior_edges(self):
        yield from (e for e in self.edges if all(isinstance(v, int) for v in (e[0][0], e[1][0])))

    @property
    def in_edges(self):
        yield from (e for e in self.edges if e[0][0]=='In')

    @property
    def out_edges(self):
        yield from (e for e in self.edges if e[1][0]=='Out')

    @property
    def op_dict(self):
        cnt = {}
        for i, op in enumerate(self.op_names):
            cnt.setdefault(op, []).append(i)
        return cnt

    def __str__(self):
        ret = ",".join([f"{i}:{op}" for i, op in enumerate(self.op_names)]) + "\n  "
        return ret + "\n  ".join(f"{l} -> {r}" for l,r in self.edges)


@dataclass
class SymOpts:
    comm: bool = False
    same_op: bool = False
    input_perm: bool = False


class PatternEncoding:
    def __init__(
        self,
        comb_type: tp.Tuple[tp.Iterable[Type], tp.Iterable[Type]],
        op_list: tp.List[Comb],
        const_list: tp.Tuple[int] = (),
        prefix: str = "",
        sym_opts: SymOpts = SymOpts(),
    ):
        self.comb_type = comb_type
        self.op_list = op_list
        self.const_list = const_list
        self.prefix = prefix
        self.sym_opts = sym_opts

        if len(self.const_list) > 0:
            raise NotImplementedError()
        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")
        iTs, oTs = self.comb_type

        # Structure
        input_vars = [get_var(f"{self.prefix}_In[{i}]", T) for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        output_vars = [get_var(f"{self.prefix}_Out[{i}]", T) for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{self.prefix}_OpIn[{opi}][{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{self.prefix}_OpOut[{opi}][{i}]", T) for i, T in enumerate(op_oTs)])
        self.input_vars = input_vars
        self.output_vars = output_vars
        self.op_out_vars = op_out_vars
        self.op_in_vars = op_in_vars
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)

    @property
    def P_lib(self):
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*self.op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(self.op_out_vars[i][j] == op_out_var)
        return fc.And(P_lib)

    @property
    def P_conn(self):
        raise NotImplementedError()

    @property
    def P_wfp(self):
        raise NotImplementedError()

    @property
    def P_sym_same_op(self):
        raise NotImplementedError()

    @property
    def P_sym_comm(self):
        raise NotImplementedError()

    @property
    def P_sym_input_perm(self):
        raise NotImplementedError()

    @property
    def P_sym(self):
        P_sym = []
        if self.sym_opts.comm:
            P_sym.append(self.P_sym_comm)
        if self.sym_opts.same_op:
            P_sym.append(self.P_sym_same_op)
        return fc.And(P_sym)


    def pattern_from_sol(self, sol):
        raise NotImplementedError()


