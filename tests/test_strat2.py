from comb.compiler import compile_program
from comb.synth import BuckSynth, verify
import pytest


import itertools as it
from comb.stdlib import GlobalModules
BV = GlobalModules['bv']
import hwtypes as ht

#Stat2 is the following:
# Given:
#   N LHS instructions,
#   M RHS instructions,
#   A Type Signature (Inputs and outputs)
#       Really this is an input multiset and output multiset of Basic types
# Synthesize two programs that are equal to each other with the correct type signature
#
# Original Query
#  Exists(L1) Forall(V1) P1_wfp(L1) & (P1_lib & P1_conn) => P1_spec
#  Exists(L1, L2) Forall(V1, V2) P1_wfp(L1) & P2_wfp(L2) & (P1_lib & P1_conn & P2_lib & P2_conn) => (I1==I2 => O1==O2)

def stat2(lhs_set, rhs_set, T_set):
    pass


def test_strat2():
    lhs = [BV.add[16], BV.mul[16]]
    rhs = [BV.add[16], BV.mul[16], BV.mul[16]]
    iT = [ht.BitVector[16] for _ in range(3)]
    oT = [ht.BitVector[16] for _ in range(1)]
    stat2(lhs_set=lhs, rhs_set=rhs, T_set=(iT, oT))
