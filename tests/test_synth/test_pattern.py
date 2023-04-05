import itertools

from comb.synth.pattern import Pattern, SymOpts

from comb.frontend.stdlib import GlobalModules
BV = GlobalModules['bv']

def test_pattern_eq():
    N = 16
    ops = [BV.add[N], BV.add[N], BV.not_[N]]
    ps = [Pattern([N,N,N], [N], ops) for _ in range(3)]
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
    for edges, p in zip(edges_list, ps):
        for e in edges:
            p.add_edge(*e)
    opts = SymOpts(comm=False,same_op=True, input_perm=True)
    for pa, pb in itertools.combinations(ps, 2):
        assert pa.equal(pb, opts)
