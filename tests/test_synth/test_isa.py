import os

from comb.frontend.compiler import compile_program

dir = os.path.dirname(os.path.realpath(__file__))
fname = f"{dir}/combs/gauss.comb"

def test_isa():
    with open(fname, 'r') as f:
        obj = compile_program(f.read())
    isa = [obj.get(f"isa.I{i}") for i in range(6)]
    ir = [obj.get(f"isa.I{i}") for i in range(3)]
    assert all(v for v in isa)
    assert all(v for v in ir)



