import pytest

from comb.frontend.compiler import compile_program
from comb.frontend.stdlib import GlobalModules
from comb.synth.comm_synth import get_comm_info, check_comm_equal, set_comm
from comb.synth.solver_utils import SolverOpts

BV = GlobalModules['bv']

add_file = '''
Comb test.add2
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
Out o0 : BV[N]
o0 = bv.add[N](i0, i1)

Comb test.sub2
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
Out o0 : BV[N]
o0 = bv.sub[N](i0, i1)

Comb test.add3
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i1)
o0 = bv.add[N](i2, t0)

Comb test.add4
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
In i3 : BV[N]
Out o0 : BV[N]
t1 = bv.add[N](i2, i3)
t0 = bv.add[N](i0, i1)
o0 = bv.add[N](t0, t1)

Comb test.add5
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
In i3 : BV[N]
In i4 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i1)
t1 = bv.add[N](i2, i3)
t2 = bv.add[N](i4, t0)
o0 = bv.add[N](t1, t2)

Comb test.amul
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
In i3 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i2)
t1 = bv.add[N](i1, i3)
o0 = bv.mul[N](t0, t1)

Comb test.foo
Param N: Int
In i0 : BV[N]
In i1 : BV[N]
In i2 : BV[N]
Out o0 : BV[N]
t0 = bv.add[N](i0, i2)
o0 = bv.sub[N](i1, t0)


'''

@pytest.mark.parametrize('num_adds', range(1,5))
def test_add_comm(num_adds):
    N = 16
    obj = compile_program(add_file)
    spec = obj.get("test", f"add{num_adds+1}")[N]
    opts=SolverOpts(
        max_iters=1000,
        verbose=2,
    )
    vals = get_comm_info(spec, opts)
    assert check_comm_equal(vals, [range(num_adds+1)])


def test_amul_comm():
    N = 16
    obj = compile_program(add_file)
    spec = obj.get("test", "amul")[N]
    set_comm(spec)
    print(spec.comm_info)
    assert check_comm_equal(spec.comm_info, [[0, 2], [1, 3]])

#Test non-commutative
def test_foo_comm():
    N = 16
    obj = compile_program(add_file)
    spec = obj.get("test", "foo")[N]
    set_comm(spec)
    print(spec.comm_info)
    assert check_comm_equal(spec.comm_info, [[0, 2], [1]])