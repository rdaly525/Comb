import itertools
import typing as tp

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import PatternEncoding, SymOpts, Pattern
from .solver_utils import SolverOpts, Cegis, get_var, smt_is_sat
from .utils import _make_list, type_to_nT, _list_to_dict, _to_int
import itertools as it


def _swap(vals, ia, ib):
    assert ia < ib
    return [*vals[:ia], vals[ib], *vals[ia+1:ib], vals[ia], *vals[ib+1:]]

def get_comm_info(spec: Comb, opts: SolverOpts=SolverOpts()):
    iT, oT = spec.get_type()
    iT = [type_to_nT(t) for t in iT]

    in_vars = [get_var(f"I{i}", n) for i, n in enumerate(iT)]
    base_outs = _make_list(spec.evaluate(*in_vars))
    sets = {}
    for n, ids in _list_to_dict(iT).items():
        if len(ids)==1:
            continue
        for ia, ib in it.combinations(ids, 2):
            assert ia < ib
            outs = _make_list(spec.evaluate(*_swap(in_vars, ia, ib)))
            outs_eq = fc.And([outA==outB for outA, outB in zip(base_outs, outs)])
            f = (~outs_eq.to_hwtypes()).value
            print(outs_eq.serialize())
            is_comm = not smt_is_sat(f, opts)
            if is_comm:
                sets.setdefault(ia, {ia}).add(ib)
                sets.setdefault(ib, {ib}).add(ia)
    ret = set(frozenset(s) for s in sets.values())