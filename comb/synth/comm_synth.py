import itertools
import typing as tp

from hwtypes import smt_utils as fc

from ..frontend.ir import Comb
from .solver_utils import SolverOpts, Cegis, get_var, smt_is_sat
from .utils import _make_list, type_to_nT, _list_to_dict, _to_int
import itertools as it

from ..frontend.ast import IntType


def _swap(vals, ia, ib):
    assert ia < ib
    return [*vals[:ia], vals[ib], *vals[ia+1:ib], vals[ia], *vals[ib+1:]]

def get_comm_info(spec: Comb, opts: SolverOpts):
    pvals = tuple(16 for _ in spec.param_types)
    if len(pvals) > 0:
        spec_n = spec[pvals]
    else:
        spec_n = spec
    iT, oT = spec_n.get_type()
    if any([isinstance(t, IntType) for t in iT]):
        return tuple([[i] for i in range(len(iT))])
    iT = [type_to_nT(t) for t in iT]
    if len(iT)==0:
        return  ([],)
    in_vars = [get_var(f"I{i}", n) for i, n in enumerate(iT)]
    base_outs = _make_list(spec_n.evaluate(*in_vars))
    sets = {i:{i} for i in range(len(iT))}
    for n, ids in _list_to_dict(iT).items():
        if len(ids)==1:
            continue
        for ia, ib in it.combinations(ids, 2):
            assert ia < ib
            outs = _make_list(spec_n.evaluate(*_swap(in_vars, ia, ib)))
            outs_eq = fc.And([outA==outB for outA, outB in zip(base_outs, outs)])
            f = (~outs_eq.to_hwtypes()).value
            is_comm = not smt_is_sat(f, opts)
            if is_comm:
                sets.setdefault(ia, {ia}).add(ib)
                sets.setdefault(ib, {ib}).add(ia)
    ret = set(frozenset(s) for s in sets.values())
    for s0, s1 in it.combinations(ret, 2):
        assert s0 & s1 == frozenset()
    return tuple(sorted(s) for s in ret)


def set_comm(op: Comb, opts: SolverOpts=SolverOpts()):
    info = get_comm_info(op, opts)
    op.comm_info = info

def check_comm_equal(comm0, comm1):
    vs = [set(frozenset(s) for s in comm) for comm in (comm0, comm1)]
    return (vs[0] == vs[1])