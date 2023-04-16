import collections
import functools
import typing as tp
import itertools as it

from comb.frontend.ast import Type, BoolType, TypeCall, BVType, IntValue, CBVType


def _list_to_counts(vals):
    ret = {}
    for v in vals:
        ret[v] = ret.get(v, 0) + 1
    return ret

def _list_to_dict(vals):
    d = {}
    for i, v in enumerate(vals):
        d.setdefault(v, []).append(i)
    return d

def bucket_combinations(vals: tp.Iterable[tp.Any], buckets: tp.List[int]):
    assert len(vals) == sum(buckets)
    if len(buckets)==0:
        yield []
    else:
        for c_vals in it.combinations(vals, buckets[0]):
            new_vals = set(vals)-set(c_vals)
            for rest_vals in bucket_combinations(new_vals, buckets[1:]):
                yield [c_vals] + rest_vals


def flat(l: tp.Iterable[tp.List[tp.Any]]) -> tp.List[tp.Any]:
    return [l__ for l_ in l for l__ in l_]

nT = collections.namedtuple('nT', 'n, const')
def nT_str(self):
    if self.const:
        return f"C{self.n}"
    else:
        return f"N{self.n}"

nT.__str__ = nT_str

def type_to_nT(T: TypeCall):
    assert isinstance(T, TypeCall)
    n = T.pargs[0].value
    assert isinstance(n, int)
    assert isinstance(T.type, (CBVType, BVType))
    const = isinstance(T.type, CBVType)
    return nT(n, const)

def nT_to_type(T: nT):
    if T.const:
        t = CBVType()
    else:
        t = BVType()
    return TypeCall(t, [IntValue(T.n)])


def types_to_nTs(Ts):
    Ns = [type_to_nT(t) for t in Ts]
    return _list_to_dict(Ns)

def types_to_nT_cnts(Ts):
    Ns = [type_to_nT(t) for t in Ts]
    return _list_to_counts(Ns)


def _to_int(x):
    assert x.is_constant()
    return int(x.constant_value())

def model_to_str(sol):
    sol_str = [f"{k}: {_to_int(v)}" for k,v in sol.items()]
    return "(" + ", ".join(sol_str) + ")"

def _make_list(v):
    if not isinstance(v, (list, tuple)):
        return [v]
    else:
        return list(v)


def _unwrap_list(v):
    if isinstance(v, (list, tuple)) and len(v)==1:
        return v[0]
    else:
        return v


def ret_list(f):
    @functools.wraps(f)
    def dec(*args, **kwargs):
        return _make_list(f(*args, **kwargs))
    return dec


def sub_cnts(acnt, bcnt):
    sub = {}
    for k in (set(acnt.keys())|(set(bcnt.keys()))):
        sub[k] = acnt.get(k,0) - bcnt.get(k,0)
    return sub

def add_cnts(acnt, bcnt):
    sub = {}
    for k in (set(acnt.keys())|(set(bcnt.keys()))):
        sub[k] = acnt.get(k,0) + bcnt.get(k,0)
    return sub

def ge0_cnts(cnts):
    return all(v>=0 for v in cnts.values())
