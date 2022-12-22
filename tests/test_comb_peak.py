import hwtypes as ht
from peak import family_closure, Peak

from comb.ast import QSym
from comb.comb_peak import CombPeak
import pytest

SBV = ht.SMTBitVector
BV = ht.BitVector
@family_closure
def add4_fc(family):
    @family.assemble(locals(), globals())
    class Add4(Peak):
        def __call__(self, x: BV[4], y: BV[4]) -> BV[4]:
            return x + y
    return Add4

def addN(N: int):
    @family_closure
    def addN_fc(family):
        @family.assemble(locals(), globals())
        class AddN(Peak):
            def __call__(self, x: BV[N], y: BV[N]) -> BV[N]:
                return x + y
        return AddN
    return addN_fc

def eval_smt_true(expr: ht.SMTBit):
    assert expr.value.is_constant()
    assert expr.value.constant_value() is True

def test_add4():

    class Add4(CombPeak):
        name = QSym("peak", "Add4")
        def __init__(self):
            super().__init__(lambda : add4_fc, 0, lambda : ((4,4), 4))

    add4 = add4_fc.SMT()
    eval_smt_true(add4(SBV[4](3), SBV[4](2)) == SBV[4](5))
    comb = Add4()
    ret = comb.evaluate(SBV[4](3), SBV[4](2))
    eval_smt_true(ret == SBV[4](5))

@pytest.mark.parametrize("N", range(4, 10))
def test_addN(N):
    class AddN(CombPeak):
        name = QSym("peak", "AddN")
        def __init__(self):
            super().__init__(addN, 1, lambda N: ((N, N), N))

    comb = AddN()
    ret = comb[N].evaluate(SBV[N](3), SBV[N](2))
    eval_smt_true(ret == SBV[N](5))



