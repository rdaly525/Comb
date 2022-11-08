import hwtypes as ht
from .ast import Module, QSym, IntType, TypeCall, BVType, Expr, IntValue, BVValue
from .ir import Modules, CombPrimitive, CallExpr


class IntBinaryOp(CombPrimitive):
    def get_type(self, *pargs):
        assert len(pargs) == 0
        return [IntType(), IntType()], [IntType()]

class IntAdd(IntBinaryOp):
    name = QSym("i","add")
    def eval(self, *args, pargs):
        assert len(pargs) == 0
        assert len(args) == 2
        i0, i1 = args
        if isinstance(i0, IntValue) and isinstance(i1, IntValue):
            return IntValue(i0.value + i1.value)
        return CallExpr(self, pargs, args)

class IntMul(IntBinaryOp):
    name = QSym("i","mul")
    def eval(self, *args, pargs):
        assert len(pargs) == 0
        assert len(args) == 2
        i0, i1 = args
        if isinstance(i0, IntValue) and isinstance(i1, IntValue):
            return IntValue(i0.value * i1.value)
        return CallExpr(self, pargs, args)

class IntModule(Module):
    # Types
    name = 'i'

    prim_map = dict(
        add=IntAdd(),
        mul=IntMul(),
    )
    def comb_from_sym(self, qsym: QSym):
        assert qsym.module == self.name
        if qsym.name not in self.prim_map:
            raise NotImplementedError()
        return self.prim_map[qsym.name]


class BVConst(CombPrimitive):
    name = QSym('bv', 'const')
    param_types = [IntType()]

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [IntType()], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==1
        N = pargs[0]
        val = args[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if isinstance(val, IntValue) and isinstance(val.value, int):
                return BVValue(ht.SMTBitVector[N.value](val.value))
        return CallExpr(self, pargs, args)


class BVAdd(CombPrimitive):
    name = QSym('bv', 'add')
    param_types = [IntType()]

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [BVCall, BVCall], [BVCall]

    def eval(self, *args, pargs):
        if len(pargs)==1 and len(args)==2:
            N = pargs[0]
            if isinstance(N, IntValue) and isinstance(N.value, int):
                if all(isinstance(arg, BVValue) for arg in args):
                    return BVValue(args[0].value + args[1].value)
        return CallExpr(self, pargs, args)
        #return i0 + i1

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


GlobalModules = dict(
    bv=BitVectorModule(),
    i=IntModule(),
)

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
