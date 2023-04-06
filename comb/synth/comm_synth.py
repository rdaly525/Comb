import itertools
import typing as tp

from hwtypes import smt_utils as fc

from comb import Comb
from .pattern import PatternEncoding, SymOpts, Pattern
from .solver_utils import SolverOpts, Cegis, get_var
from .utils import _make_list, type_to_N, _list_to_dict, _to_int
import itertools as it


def _swap(vals, ia, ib):
    assert ia < ib
    return [*vals[:ia], vals[ib], *vals[ia+1:ib], vals[ia], *vals[ib+1:]]

class CommSynth(Cegis):
    def __init__(
        self,
        spec: Comb,
    ):
        self.spec = spec
        iT, oT = spec.get_type()
        self.iT = [type_to_N(t) for t in iT]

        pairs = []
        inds = {} #inds[n][pair] = ind
        E_vars = []
        for n, ids in _list_to_dict(iT).items():
            if len(ids)==1:
                continue
            for ia,ib in it.combinations(ids, 2):
                in_vars = [get_var(f"I{i}_({ia},{ib})", n) for i, n in enumerate(iT)]
                base_outs = _make_list(spec.evaluate(*in_vars))
                assert ia < ib
                ind = get_var(f"ind[{ia},{ib}]", 0)
                E_vars.append(ind)
                inds.setdefault(n, {})[(ia, ib)] = ind
                outs = _make_list(spec.evaluate(*_swap(in_vars, ia, ib)))
                outs_eq = fc.And([outA==outB for outA, outB in zip(base_outs, outs)])
                pairs.append(outs_eq.to_hwtypes()==ind)
        self.inds = inds
        query = fc.And(pairs)
        print(query.serialize())
        super().__init__(query.to_hwtypes(), E_vars)

    def get_comm(self, opts: SolverOpts = SolverOpts()) -> tp.Set[tp.Set[int]]:
        sols = []
        for sol in self.cegis_all(opts):
            sols.append(sol)
        assert len(sols)==1
        sets = {}
        for n, pairs in self.inds.items():
            for (ia, ib), ind in pairs.items():
                ind_val = _to_int(sol[ind.value])
                if ind_val:
                    sets.setdefault(ia, {ia}).add(ib)
                    sets.setdefault(ib, {ib}).add(ia)
        return set(frozenset(s) for s in sets.values())
