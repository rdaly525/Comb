from comb.frontend.compiler import  compile_program
import pytest
from comb.frontend.ir import Obj

p_obj0 = \
''' \
Comb test.t1
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0 = bv.add[16](i0, i1)
o = bv.add[16](t0, t0)

Comb test.t2
In i0 : BV[16]
In i1 : BV[16]
Out o : BV[16]
t0 = test.t1(i0, i1)
o = bv.add[16](t0, t0)
'''

@pytest.mark.parametrize("p", [
    p_obj0,
])
def test_obj(p):
    obj: Obj = compile_program(p)
    assert 'test.t1' in obj.comb_dict
    assert 'test.t2' in obj.comb_dict
    p1 = obj.serialize()
    obj1 = compile_program(p)
    assert obj1.serialize()==p1
