import itertools

from comb.synth.pattern import Pattern, SymOpts

from comb.frontend.stdlib import GlobalModules
from comb.synth.utils import nT

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