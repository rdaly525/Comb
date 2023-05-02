import hwtypes as ht
from comb.frontend.ast import Module, QSym, IntType, TypeCall, BVType, Expr, IntValue, BVValue, CBVType
from comb.frontend.comb_peak import CombPeak
from comb.frontend.ir import CombPrimitive, CallExpr, CombSpecialized


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

class IntSub(IntBinaryOp):
    name = QSym("i","add")
    def eval(self, *args, pargs):
        assert len(pargs) == 0
        assert len(args) == 2
        i0, i1 = args
        if isinstance(i0, IntValue) and isinstance(i1, IntValue):
            return IntValue(i0.value - i1.value)
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

    def __init__(self):
        super().__init__('i')

    opdict = dict(
        add=IntAdd(),
        sub=IntSub(),
        mul=IntMul(),
    )
    def comb_from_sym(self, qsym: QSym):
        assert qsym.module == self.name
        if qsym.name not in self.opdict:
            raise NotImplementedError()
        return self.opdict[qsym.name]

    def get(self, name):
        return self.opdict.get(name)

class BVConst(CombPrimitive):
    name = QSym('bv', 'const')
    param_types = [IntType(), IntType()]
    num_inputs = 0
    num_outputs = 1

    def get_type(self, N: Expr, val: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==2 and len(args)==0
        N = pargs[0]
        val = pargs[1]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if isinstance(val, IntValue) and isinstance(val.value, int):
                return [BVValue(ht.SMTBitVector[N.value](val.value))]
        return CallExpr(self, pargs, args)


def create_BVUnary(class_name: str, fun):
    class BVBin(CombPrimitive):
        name = QSym('bv', class_name)
        param_types = [IntType()]
        num_inputs = 1
        num_outputs = 1
        comm_info = ([0],)

        def get_type(self, N: Expr):
            BVCall = TypeCall(BVType(), [N])
            return [BVCall], [BVCall]

        def eval(self, *args, pargs):
            assert len(pargs)==1 and len(args)==1
            N = pargs[0]
            if isinstance(N, IntValue) and isinstance(N.value, int):
                if all(isinstance(arg, BVValue) for arg in args):
                    return [BVValue(fun(args[0].value))]
            return CallExpr(self, pargs, args)

        def partial_eval(self, N):
            return CombSpecialized(self, [N])

    BVBin.__name__ = "BV"+class_name.capitalize()
    return BVBin()

#Represents an abstract constant :: CBV -> BV
class AbsConst(CombPrimitive):
    name = QSym('bv', 'abs_const')
    param_types = [IntType()]
    num_inputs = 1
    num_outputs = 1
    comm_info = ([0],)

    def get_type(self, N: Expr):
        return [TypeCall(CBVType(), [N])], [TypeCall(BVType(), [N])]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==1
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if all(isinstance(arg, BVValue) for arg in args):
                return [args[0]]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

def create_BVBinary(class_name: str, fun, comm):
    class BVBin(CombPrimitive):
        name = QSym('bv', class_name)
        param_types = [IntType()]
        comm_info = ([0,1],) if comm else ([0], [1])
        num_inputs = 2
        num_outputs = 1

        def get_type(self, N: Expr):
            BVCall = TypeCall(BVType(), [N])
            return [BVCall, BVCall], [BVCall]

        def eval(self, *args, pargs):
            assert len(pargs)==1 and len(args)==2
            N = pargs[0]
            if isinstance(N, IntValue) and isinstance(N.value, int):
                if all(isinstance(arg, BVValue) for arg in args):
                    return [BVValue(fun(args[0].value, args[1].value))]
            return CallExpr(self, pargs, args)

        def partial_eval(self, N):
            return CombSpecialized(self, [N])

    BVBin.__name__ = "BV"+class_name.capitalize()
    return BVBin()

def create_BVComp(class_name: str, fun, comm):
    class BVComp(CombPrimitive):
        name = QSym('bv', class_name)
        param_types = [IntType()]
        comm_info = ([0,1],) if comm else ([0], [1])
        num_inputs = 2
        num_outputs = 1

        def get_type(self, N: Expr):
            BVCall = TypeCall(BVType(), [N])
            return [BVCall, BVCall], [BVCall]

        def eval(self, *args, pargs):
            assert len(pargs)==1 and len(args)==2
            N = pargs[0]
            if isinstance(N, IntValue) and isinstance(N.value, int):
                if all(isinstance(arg, BVValue) for arg in args):
                    bv0 = ht.SMTBitVector[N.value](0)
                    bv1 = ht.SMTBitVector[N.value](1)
                    v = fun(args[0].value, args[1].value)
                    assert isinstance(v, ht.SMTBit)
                    return [BVValue(v.ite(bv1, bv0))]
            return CallExpr(self, pargs, args)

        def partial_eval(self, N):
            return CombSpecialized(self, [N])

    BVComp.__name__ = "BV"+class_name.capitalize()
    return BVComp()

_binops = dict(
    add=(lambda x, y: x + y, True),
    sub=(lambda x, y: x - y, False),
    mul=(lambda x, y: x * y, True),
    and_=(lambda x, y: x & y, True),
    or_=(lambda x, y: x | y, True),
    xor=(lambda x, y: x ^ y, True),
    lshr=(lambda x, y: x << y, True),
)

_cmpops = dict(
    eq=(lambda x, y: x==y, True),
    neq=(lambda x, y: ~(x==y), True),
    ult=(lambda x, y: x.bvult(y), False),
    slt=(lambda x, y: x.bvslt(y), False),
    ule=(lambda x, y: x.bvule(y), False),
    sle=(lambda x, y: x.bvsle(y), False),
    ugt=(lambda x, y: x.bvugt(y), False),
    sgt=(lambda x, y: x.bvsgt(y), False),
    uge=(lambda x, y: x.bvuge(y), False),
    sge=(lambda x, y: x.bvsge(y), False),
)

_unary_ops = dict(
    identity=lambda x: x,
    neg=lambda x: -x,
    not_=lambda x: ~x,
)


from peak import family_closure, Peak
def concat_peak(lsbs, msbs):
    BV = ht.BitVector
    @family_closure
    def concat_fc(family):
        @family.assemble(locals(), globals())
        class Concat(Peak):
            def __call__(self, x: BV[lsbs], y: BV[msbs]) -> BV[lsbs+msbs]:
                return x.concat(y)
        return Concat
    return concat_fc

class BVConcat(CombPeak):
    name = QSym("bv", "concat")
    def __init__(self):
        super().__init__(concat_peak, 2, lambda lsbs, msbs: ((lsbs, msbs), lsbs+msbs))


def slice_peak(o, l, h):
    BV = ht.BitVector
    @family_closure
    def slice_fc(family):
        @family.assemble(locals(), globals())
        class Slice(Peak):
            def __call__(self, x: BV[o]) -> BV[o+l-h]:
                return x[l:h]
        return Slice
    return slice_fc

class BVSlice(CombPeak):
    name = QSym("bv", "slice")
    def __init__(self):
        super().__init__(slice_peak, 3, lambda o, l, h: (o, o - (h-l)))


class BitVectorModule(Module):
    # Types
    def __init__(self):
        super().__init__('bv')
        opdict = dict(
            const=BVConst(),
            abs_const=AbsConst(),
            concat=BVConcat(),
            slice=BVSlice(),
        )
        for name, (fun, comm) in _binops.items():
            opdict[name] = create_BVBinary(name, fun, comm)
        for name, (fun, comm) in _cmpops.items():
            opdict[name] = create_BVComp(name, fun, comm)
        for name, fun in _unary_ops.items():
            opdict[name] = create_BVUnary(name, fun)
        self.opdict = opdict

    def __getattr__(self, item):
        if item in self.opdict:
            return self.opdict[item]
        raise AttributeError()


    def comb_from_sym(self, qsym: QSym):
        assert qsym.module == self.name
        if qsym.name in self.opdict:
            return self.opdict[qsym.name]
        #if qsym.name in _binops:
        #    return BVBinary(*qsym.genargs, qsym.name)
        #elif qsym.name in _unary_ops:
        #    return BVUnary(*qsym.genargs, qsym.name)
        raise NotImplementedError(str(qsym))


GlobalModules = dict(
    bv=BitVectorModule(),
    i=IntModule(),
)

#Return a call expression
def make_bv_const(N: int, val: int) -> CallExpr:
    const = GlobalModules['bv'].const
    return CallExpr(const, [IntValue(N)], [IntValue(val)])


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
