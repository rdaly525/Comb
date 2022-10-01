import hwtypes as ht
from .ast import Module, QSym, IntType, TypeCall, Type, ParamTerm, BVType
from .ir import Modules, CombPrimitive

class IntModule(Module):
    # Types
    name = 'i'

    def comb_from_sym(self, qsym: QSym):
        assert qsym.module == self.name
        raise NotImplementedError()


class BVConst(CombPrimitive):
    name = QSym('bv','const')
    param_types = [IntType()]

    def get_type(self, N: ParamTerm):
        BVCall = TypeCall(BVType(), N)
        return [IntType()], [BVCall]

class BVConst(CombPrimitive):
    name = QSym('bv', 'const')
    param_types = [IntType()]

    def get_type(self, N: ParamTerm):
        BVCall = TypeCall(BVType(), N)
        return [IntType()], [BVCall]


class BVAdd(CombPrimitive):
    name = QSym('bv','add')
    param_types = [IntType()]

    def get_type(self, N: ParamTerm):
        BVCall = TypeCall(BVType(), N)
        return [BVCall, BVCall], [BVCall]

    #def input_types(self, N: Type):
    #    return [BVType(N), BVType(N)]

    #def output_types(self, N):
    #    return [BVType(N)]


class BitVectorModule(Module):
    # Types
    name = 'bv'

    def comb_from_sym(self, qsym: QSym):
        assert qsym.module == self.name
        if qsym.name == "add":
            return BVAdd()
        elif qsym.name == "const":
            return BVConst()
        #if qsym.name in _binops:
        #    return BVBinary(*qsym.genargs, qsym.name)
        #elif qsym.name in _unary_ops:
        #    return BVUnary(*qsym.genargs, qsym.name)
        raise NotImplementedError()


Modules['bv'] = BitVectorModule()
Modules['i'] = IntModule()

#class Bool:
#    name = QSym('bv', 'bool')
#    def free_var(self, name):
#        return ht.SMTBit(prefix=name)
#
#
#_binops = dict(
#    add=(lambda x, y: x + y, True),
#    sub=(lambda x, y: x - y, False),
#    mul=(lambda x, y: x * y, True),
#)
#
#_unary_ops = dict(
#    identity=lambda x: x,
#    neg=lambda x: -x,
#    not_=lambda x: ~x,
#)
#
#class BVUnary(Prim):
#    commutative = False
#    def __init__(self, N, op):
#        self.N = N
#        self.name = QSym("bv", op, (N,))
#        assert op in _unary_ops
#        self.op = _unary_ops[op]
#        bv_t = QSym('bv','bv',(N,))
#        self.inputs = (Var('i0', bv_t),)
#        self.outputs = (Var('o0',bv_t),)
#        bv_t = BitVectorModule().type_from_sym(bv_t)
#        self.sym_table = dict(
#            i0=bv_t,
#            o0=bv_t,
#        )
#
#
#    def eval(self, a):
#        return (self.op(a),)
#
#
#class BVBinary(Prim):
#    def __init__(self, N, op):
#        self.N = N
#        self.name = QSym("bv", op, (N,))
#        assert op in _binops
#        self.op, self.commutative = _binops[op]
#        bv_t = QSym('bv','bv',(N,))
#        self.inputs = (Var('i0', bv_t), Var('i1', bv_t))
#        self.outputs = (Var('o0',bv_t),)
#        bv_t = BitVectorModule().type_from_sym(bv_t)
#        self.sym_table = dict(
#            i0=bv_t,
#            i1=bv_t,
#            o0=bv_t,
#        )
#
#
#    def eval(self, a, b):
#        return (self.op(a, b),)
