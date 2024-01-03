import itertools
import pytest

from comb.synth.pattern import Pattern, SymOpts, PatternMatcher

from comb.frontend.stdlib import GlobalModules
from comb.synth.utils import nT
from collections import OrderedDict

BV = GlobalModules['bv']

def test_pattern_eq():
    N = 16
    ops = [BV.add[N], BV.add[N], BV.not_[N]]
    T = nT(N,False)
    edges_list = [
        [
            ((-1, 0), (0, 0)),
            ((-1, 1), (0, 1)),
            ((-1, 2), (1, 0)),
            ((0, 0), (1, 1)),
            ((1, 0), (2, 0)),
            ((2, 0), (3, 0)),
        ],
        [ #Swap inputs
            ((-1, 1), (0, 0)),
            ((-1, 2), (0, 1)),
            ((-1, 0), (1, 0)),
            ((0, 0), (1, 1)),
            ((1, 0), (2, 0)),
            ((2, 0), (3, 0)),
        ],
        [ #Swap ops
            ((-1, 0), (1, 0)),
            ((-1, 1), (1, 1)),
            ((-1, 2), (0, 0)),
            ((1, 0), (0, 1)),
            ((0, 0), (2, 0)),
            ((2, 0), (3, 0)),
        ],
    ]
    ps = [Pattern([T,T,T], [T], ops, es, []) for es in edges_list]
    for pa, pb in itertools.combinations(ps, 2):
        assert pa.equal(pb)
        assert pb.equal(pa)

def test_comm_edge():
    N = 16
    ops = [BV.add[N], BV.add[N]]
    T = nT(N,False)
    edges_list = [
        [
            ((-1, 0), (0, 0)),
            ((-1, 0), (1, 1)),
            ((-1, 1), (1, 0)),
            ((0, 0), (2, 0)),
            ((1, 0), (0, 1)),
        ],
        [
            ((-1, 0), (0, 0)),
            ((-1, 0), (1, 1)),
            ((-1, 1), (0, 1)),
            ((0, 0), (1, 0)),
            ((1, 0), (2, 0)),
        ],
    ]
    ps = [Pattern([T,T], [T], ops, es, []) for es in edges_list]
    pa = ps[0]
    print(pa.to_comb('a','a'))
    pb = ps[1]
    print(pb.to_comb('b','b'))
    opts = SymOpts(comm=True,same_op=True, input_perm=False)
    assert pb.equal(pa)
    assert pa.equal(pb)


@pytest.mark.parametrize("ops", [
    (SymOpts(False, True, False)),
    (SymOpts(True, True, False)),
])
def test_pattern_matcher(ops):

    N = 4

    adder = BV.add[N]
    from_edges = [((-1,0),(0,0)), ((-1,1),(0,1)), ((-1,2), (1,0)), ((0,0),(1,1)), ((1,0), (2,0)), ((0,0),(2,1))]
    from_pat = Pattern(adder.get_type()[0], adder.get_type()[1]*2, [adder, adder], from_edges, [])

    to_edges = [((-1,0),(0,0)), ((-1,1),(0,1)), 
                ((-1,2), (1,0)), ((-1,3),(1,1)), 
                ((0,0), (2,0)), ((1,0),(2,1)), 
                ((2,0), (3,0))]
    to_pat = Pattern(adder.get_type()[0], adder.get_type()[1], [adder, adder, adder], to_edges, [])
    pm = PatternMatcher(from_pat, to_pat, ops)
    matches = pm.match_all()
    if ops.comm:
        print(sorted(d.to_tuple() for d in matches))
        assert sorted(d.to_tuple() for d in matches) == [
                ((((-1, 0), (-1, 0)), ((-1, 1), (-1, 1)), ((-1, 2), (1, 0))), ((0, 0), (1, 2)), (((0, 0), (-1, 0)), ((0, 1), (-1, 1)), ((1, 0), (1, 0)), ((1, 1), (0, 0)))), 
                ((((-1, 0), (-1, 1)), ((-1, 1), (-1, 0)), ((-1, 2), (1, 0))), ((0, 0), (1, 2)), (((0, 0), (-1, 1)), ((0, 1), (-1, 0)), ((1, 0), (1, 0)), ((1, 1), (0, 0)))), 
                ((((-1, 0), (-1, 2)), ((-1, 1), (-1, 3)), ((-1, 2), (0, 0))), ((0, 1), (1, 2)), (((0, 0), (-1, 2)), ((0, 1), (-1, 3)), ((1, 0), (0, 0)), ((1, 1), (1, 0)))), 
                ((((-1, 0), (-1, 3)), ((-1, 1), (-1, 2)), ((-1, 2), (0, 0))), ((0, 1), (1, 2)), (((0, 0), (-1, 3)), ((0, 1), (-1, 2)), ((1, 0), (0, 0)), ((1, 1), (1, 0))))
            ]
    else:
        assert sorted(d.to_tuple() for d in matches) == [
          ((((-1, 0),(-1, 2)), ((-1, 1),(-1, 3)), ((-1, 2),(0, 0))), 
          ((0,1), (1,2)), 
          (((0, 0),(-1, 2)), ((0, 1),(-1, 3)), ((1, 0),(0, 0)), ((1, 1),(1, 0))))]

@pytest.mark.parametrize("ops", [
    (SymOpts(False, True, False)),
    (SymOpts(True, True, False)),
])
def test_pattern_matcher_dont_cares_0(ops):
    N = 4

    adder = BV.add[N]
    dont_care = BV.dont_care[N]
    from_edges = [((-1,0),(0,0)), ((2,0),(0,1)), ((2,0), (1,0)), ((0,0),(1,1)), ((1,0), (3,0)), ((0,0),(3,1))]
    from_pat = Pattern(adder.get_type()[0], adder.get_type()[1]*2, [adder, adder, dont_care], from_edges, [])

    to_edges = [((-1,0),(0,0)), ((-1,1),(0,1)), 
                ((-1,2), (1,0)), ((-1,3),(1,1)), 
                ((0,0), (2,0)), ((1,0),(2,1)), 
                ((2,0), (3,0))]
    to_pat = Pattern(adder.get_type()[0], adder.get_type()[1], [adder, adder, adder], to_edges, [])
    pm = PatternMatcher(from_pat, to_pat, ops)
    matches = pm.match_all()
    assert len(matches) == 0

@pytest.mark.parametrize("ops", [
    (SymOpts(False, True, False)),
    (SymOpts(True, True, False)),
])
def test_pattern_matcher_dont_cares_1(ops):
    N = 4

    adder = BV.add[N]
    dont_care = BV.dont_care[N]
    from_edges = [((-1,0),(0,0)), ((2,0),(0,1)), ((3,0), (1,0)), ((0,0),(1,1)), ((1,0), (4,0)), ((0,0),(4,1))]
    from_pat = Pattern(adder.get_type()[0], adder.get_type()[1]*2, [adder, adder, dont_care, dont_care], from_edges, [])

    to_edges = [((-1,0),(0,0)), ((-1,1),(0,1)), 
                ((-1,2), (1,0)), ((-1,3),(1,1)), 
                ((0,0), (2,0)), ((1,0),(2,1)), 
                ((2,0), (3,0))]
    to_pat = Pattern(adder.get_type()[0], adder.get_type()[1], [adder, adder, adder], to_edges, [])
    pm = PatternMatcher(from_pat, to_pat, ops)
    matches = pm.match_all()
    if ops.comm:
        print(sorted(d.to_tuple() for d in matches))
        assert sorted(d.to_tuple() for d in matches) == [
            ((((-1, 0), (-1, 0)), ((2, 0), (-1, 1)), ((3, 0), (1, 0))), ((0, 0), (1, 2)), (((0, 0), (-1, 0)), ((0, 1), (-1, 1)), ((1, 0), (1, 0)), ((1, 1), (0, 0)))), 
            ((((-1, 0), (-1, 1)), ((2, 0), (-1, 0)), ((3, 0), (1, 0))), ((0, 0), (1, 2)), (((0, 0), (-1, 1)), ((0, 1), (-1, 0)), ((1, 0), (1, 0)), ((1, 1), (0, 0)))), 
            ((((-1, 0), (-1, 2)), ((2, 0), (-1, 3)), ((3, 0), (0, 0))), ((0, 1), (1, 2)), (((0, 0), (-1, 2)), ((0, 1), (-1, 3)), ((1, 0), (0, 0)), ((1, 1), (1, 0)))), 
            ((((-1, 0), (-1, 3)), ((2, 0), (-1, 2)), ((3, 0), (0, 0))), ((0, 1), (1, 2)), (((0, 0), (-1, 3)), ((0, 1), (-1, 2)), ((1, 0), (0, 0)), ((1, 1), (1, 0))))]
    else:
        print(sorted(d.to_tuple() for d in matches))
        assert sorted(d.to_tuple() for d in matches) == [
            ((((-1, 0), (-1, 2)), ((2, 0), (-1, 3)), ((3, 0), (0, 0))), 
            ((0, 1), (1, 2)), 
            (((0, 0), (-1, 2)), ((0, 1), (-1, 3)), ((1, 0), (0, 0)), ((1, 1), (1, 0))))]

@pytest.mark.parametrize("ops", [
    (SymOpts(False, True, False)),
    (SymOpts(True, True, False)),
])
def test_pattern_matcher_dont_cares_2(ops):
    N = 4

    adder = BV.add[N]
    dont_care = BV.dont_care[N]
    from_edges = [((1,0),(0,1)), ((1,0), (0,0)), ((0,0),(2,0))]
    from_pat = Pattern([], adder.get_type()[1], [adder, dont_care], from_edges, [])

    to_edges = [((-1,0),(0,0)), ((-1,1),(0,1)), 
                ((0,0), (1,0))]
    to_pat = Pattern(adder.get_type()[0], adder.get_type()[1], [adder], to_edges, [])
    pm = PatternMatcher(from_pat, to_pat, ops)
    matches = pm.match_all()
    assert sorted(d.to_tuple() for d in matches) == []


@pytest.mark.parametrize("ops", [
    (SymOpts(False, True, False)),
    (SymOpts(True, True, False)),
])
def test_pattern_matcher_dont_cares_2(ops):
    N = 4

    adder = BV.add[N]
    dont_care = BV.dont_care[N]
    from_edges = [((1,0),(0,1)), ((1,0), (0,0)), ((0,0),(2,0))]
    from_pat = Pattern([], adder.get_type()[1], [adder, dont_care], from_edges, [])

    to_edges = [((-1,0),(0,0)), ((-1,0),(0,1)), 
                ((0,0), (1,0))]
    to_pat = Pattern([adder.get_type()[0][0]], adder.get_type()[1], [adder], to_edges, [])
    pm = PatternMatcher(from_pat, to_pat, ops)
    matches = pm.match_all()
    assert sorted(d.to_tuple() for d in matches) == [
        ((((1, 0), (-1, 0)),), ((0, 0),), (((0, 0), (-1, 0)), ((0, 1), (-1, 0))))]