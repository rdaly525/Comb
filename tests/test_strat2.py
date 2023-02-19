from comb.compiler import compile_program
from comb.synth import BuckSynth, verify
import pytest


import itertools as it
from comb.stdlib import GlobalModules
BV = GlobalModules['bv']
import hwtypes as ht


def stat2(lhs_set, rhs_set, T_set):
    pass


def test_strat2():
    lhs = [BV.add[16], BV.mul[16]]
    rhs = [BV.add[16], BV.mul[16], BV.mul[16]]
    iT = [ht.BitVector[16] for _ in range(3)]
    oT = [ht.BitVector[16] for _ in range(1)]
    stat2(lhs_set=lhs, rhs_set=rhs, T_set=(iT, oT))
