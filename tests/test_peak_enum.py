import hwtypes as ht
from peak import family_closure, Peak, Const
from comb.exp import enumerate_peak, enumerate_adt
from comb.ast import QSym
from comb.comb_peak import CombPeak
import pytest

class Op(ht.Enum):
    Add = ht.new_instruction()
    Mul = ht.new_instruction()

class ImmKind(ht.Product):
    op1 = Op
    op2 = Op
    imm = ht.BitVector[8]

class RKind(ht.Product):
    op = Op


class TestKind(ht.Product):
    i=ImmKind
    i2=ImmKind
    op=Op
    r=RKind

class Instr(ht.adt.TaggedUnion):
    r = RKind
    i = ImmKind

BV = ht.BitVector

@family_closure
def PE_fc(family):

    @family.assemble(locals(), globals())
    class PE(Peak):
        def __call__(self, inst: Const(Instr), x: BV[8], y: BV[8]) -> BV[8]:
            if inst.r.match:
                op = inst.r.value.op
            else:
                op = inst.i.value.op
                y = inst.i.value.imm
            if op == Op.Add:
                z = x + y
            else:
                z = x * y
    return PE

def test_peak_enum():
    print(len(enumerate_adt(TestKind)))