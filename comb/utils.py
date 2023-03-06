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


def type_to_N(T: Type):
    if isinstance(T, BoolType):
        n = 0
    else:
        assert isinstance(T, TypeCall)
        assert isinstance(T.type, BVType)
        n = T.pargs[0].value
        assert isinstance(n, int)
    return n

def comb_type_to_sT(Ts):
    Ns = [type_to_N(t) for t in Ts]
    return _list_to_dict(Ns)

def _to_int(x):
    assert x.is_constant()
    return int(x.constant_value())

def print_model(sol):
    print("MODEL")
    for k, v in sol.items():
        print(f"{k}: {_to_int(v)}")

