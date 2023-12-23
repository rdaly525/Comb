import functools
import typing as tp
from functools import cached_property

from hwtypes import smt_utils as fc

from comb import Comb
from comb.synth.pattern import Pattern
from comb.synth.solver_utils import get_var
from comb.synth.utils import nT, _make_list, _list_to_counts, types_to_nT_cnts, add_cnts, ge0_cnts, sub_cnts


class PatternEncoding:
    def __init__(
        self,
        iT: tp.List[nT],
        oT: tp.List[nT],
        op_list: tp.List[Comb],
        const_list: tp.Tuple[int] = (),
        prefix: str = "",
        simplify_dont_cares: bool = False,
        simplify_gen_consts: bool = False
    ):
        self.iT = iT
        self.oT = oT
        assert all(isinstance(T, nT) for T in [*iT, *oT])
        self.op_list = op_list
        self.const_list = const_list
        self.prefix = prefix
        self.simplify_dont_cares = simplify_dont_cares
        self.simplify_gen_consts = simplify_gen_consts

        if len(self.const_list) > 0:
            raise NotImplementedError()
        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")

        # Structure
        input_vars = [get_var(f"{prefix}_In[{i}]", T) for i, T in enumerate(iT)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        output_vars = [get_var(f"{prefix}_Out[{i}]", T) for i, T in enumerate(oT)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{prefix}_OpIn[{opi}][{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{prefix}_OpOut[{opi}][{i}]", T) for i, T in enumerate(op_oTs)])
        self.input_vars = input_vars
        self.output_vars = output_vars
        self.op_out_vars = op_out_vars
        self.op_in_vars = op_in_vars
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)


    @property
    def L(self):
        raise NotImplementedError

    def P_iropt(self, dce, cse):
        P_iropt = []
        if dce:
            P_iropt.append(self.P_dse)
        if cse:
            P_iropt.append(self.P_cse)
        return fc.And(P_iropt)

    def P_narrow(self, C, K):
        P_narrow = []
        if C:
            P_narrow.append(self.P_comm)
        if K:
            P_narrow.append(self.P_K)
        return fc.And(P_narrow)


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

    @cached_property
    def num_ops(self):
        return len(self.op_list)

    def pattern_from_sol(self, sol) -> Pattern:
        raise NotImplementedError()

    def match_one_pattern(self, p: Pattern, pid_to_csid: tp.Mapping[int, int]):
        raise NotImplementedError()

    def match_rule_dag(self, dag, r_matches):
        raise NotImplementedError()

    def match_all_patterns(self, pat: Pattern):
        raise NotImplementedError()

    def any_pat_match(self, pat: Pattern):
        raise NotImplementedError()

    @cached_property
    def types_viable(self):
        iTs = _list_to_counts(self.iT)
        oTs = _list_to_counts(self.oT)
        op_iTs = [types_to_nT_cnts(op.get_type()[0]) for op in self.op_list]
        op_oTs = [types_to_nT_cnts(op.get_type()[1]) for op in self.op_list]
        snks = add_cnts(oTs, functools.reduce(lambda a, b: add_cnts(a,b), op_iTs))
        srcs = add_cnts(iTs, functools.reduce(lambda a, b: add_cnts(a,b), op_oTs))
        return set(snks.keys()) <= set(srcs.keys())
