import typing as tp
import itertools as it

from comb.ast import Type, BoolType, TypeCall, BVType


def _list_to_counts(vals):
    ret = {}
    for v in vals:
        ret[v] = ret.get(v, 0) + 1
    return ret

def _list_to_dict(vals):
    d = {}
    for i, v in enumerate(vals):
        d.setdefault(v,[]).append(i)
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

def comb_type_to_sT(T):
    Ns = []
    for i, t in enumerate(T):
        if isinstance(t, BoolType):
            n = 0
        else:
            assert isinstance(t, TypeCall)
            assert isinstance(t.type, BVType)
            n = t.pargs[0].value
            assert isinstance(n, int)
        Ns.append(n)
    return _list_to_dict(Ns)


def _to_int(x):
    assert x.is_constant()
    return int(x.constant_value())

def print_model(sol):
    print("MODEL")
    for k, v in sol.items():
        print(f"{k}: {_to_int(v)}")

