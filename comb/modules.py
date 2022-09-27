from .comb import Module, QSym, Prim, Var, Nat, NatType
import hwtypes as ht


class ParamModule(Module):
    # Types
    name = 'p'

    def type_from_sym(self, qsym: QSym):
        assert qsym.ns == self.name
        if qsym.name == "Nat":
            return NatType
        else:
            raise ValueError(f"{qsym} not found")

    def comb_from_sym(self, qsym: QSym):
        assert qsym.ns == self.name
        raise NotImplementedError()

#class BV_N:
#    def __init__(self, N: Nat):
#        self.N = N

class BVType:
    name = QSym('bv', 'bv')
    param_types = (NatType,)

    def __init__(self, N: Nat):
        self.N = N

    def free_var(self, N: int, name):
        return ht.SMTBitVector[N](prefix=name)

class Bool:
    name = QSym('bv', 'bool')
    def free_var(self, name):
        return ht.SMTBit(prefix=name)


_binops = dict(
    add=(lambda x, y: x + y, True),
    sub=(lambda x, y: x - y, False),
    mul=(lambda x, y: x * y, True),
)

_unary_ops = dict(
    identity=lambda x: x,
    neg=lambda x: -x,
    not_=lambda x: ~x,
)

class BVUnary(Prim):
    commutative = False
    def __init__(self, N, op):
        self.N = N
        self.name = QSym("bv", op, (N,))
        assert op in _unary_ops
        self.op = _unary_ops[op]
        bv_t = QSym('bv','bv',(N,))
        self.inputs = (Var('i0', bv_t),)
        self.outputs = (Var('o0',bv_t),)
        bv_t = BitVectorModule().type_from_sym(bv_t)
        self.sym_table = dict(
            i0=bv_t,
            o0=bv_t,
        )


    def eval(self, a):
        return (self.op(a),)


class BVAdd(Prim):
    param_types = [NatType]

    def input_types(self, N):
        return [BVType(N), BVType(N)]

    def output_types(self, N):
        return [BVType(N)]

class BVBinary(Prim):
    def __init__(self, N, op):
        self.N = N
        self.name = QSym("bv", op, (N,))
        assert op in _binops
        self.op, self.commutative = _binops[op]
        bv_t = QSym('bv','bv',(N,))
        self.inputs = (Var('i0', bv_t), Var('i1', bv_t))
        self.outputs = (Var('o0',bv_t),)
        bv_t = BitVectorModule().type_from_sym(bv_t)
        self.sym_table = dict(
            i0=bv_t,
            i1=bv_t,
            o0=bv_t,
        )


    def eval(self, a, b):
        return (self.op(a, b),)

class BitVectorModule(Module):
    # Types
    name = 'bv'

    def type_from_sym(self, qsym: QSym):
        assert qsym.ns == self.name
        if qsym.name == "bv":
            return BVType
        elif qsym.name == "bool":
            return Bool
        else:
            raise ValueError(f"{qsym} not found")

    def comb_from_sym(self, qsym: QSym):
        assert qsym.ns == self.name
        if qsym.name == "add":
            return BVAdd()
        #if qsym.name in _binops:
        #    return BVBinary(*qsym.genargs, qsym.name)
        #elif qsym.name in _unary_ops:
        #    return BVUnary(*qsym.genargs, qsym.name)
        raise NotImplementedError()

