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
    name = QSym("i","sub")
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

class CBVSynthConst(CombPrimitive):
    name = QSym('bv', '_synth_const')
    param_types = [IntType()]
    num_inputs = 0
    num_outputs = 1

    def get_type(self, N: Expr):
        CBVCall = TypeCall(CBVType(), [N])
        return [], [CBVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==1
        return [BVValue(args[0])]

class CBVConst(CombPrimitive):
    name = QSym('bv', 'c_const')
    param_types = [IntType(), IntType()]
    num_inputs = 0
    num_outputs = 1

    def get_type(self, N: Expr, val: Expr):
        CBVCall = TypeCall(CBVType(), [N])
        return [], [CBVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==2 and len(args)==0
        N = pargs[0]
        val = pargs[1]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if isinstance(val, IntValue) and isinstance(val.value, int):
                return [BVValue(ht.SMTBitVector[N.value](val.value))]
        return CallExpr(self, pargs, args)

class CBVDontCare(CombPrimitive):
    name = QSym('bv', 'c_dont_care')
    param_types = [IntType()]
    num_inputs = 0
    num_outputs = 1

    def get_type(self, N: Expr):
        CBVCall = TypeCall(CBVType(), [N])
        return [], [CBVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 
        if len(args) == 1:
            return [BVValue(args[0])]
        assert len(args) == 0
        #TODO: need to return a free variable here
        return [BVValue(ht.SMTBitVector[pargs[0].value](0))]

class BVDontCare(CombPrimitive):
    name = QSym('bv', 'dont_care')
    param_types = [IntType()]
    num_inputs = 0
    num_outputs = 1

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 
        if len(args) == 1:
            return [BVValue(args[0])]
        assert len(args) == 0
        #TODO: need to return a free variable here
        return [BVValue(ht.SMTBitVector[pargs[0].value](0))]

def is_dont_care(comb):
    return isinstance(comb, BVDontCare) or isinstance(comb, CBVDontCare)

class BVUnary(CombPrimitive):
    param_types = [IntType()]
    num_inputs = 1
    num_outputs = 1
    comm_info = ([0],)

    def __init__(self, class_name: str, fun):
        self.name = QSym('bv', class_name)
        self.fun = fun

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [BVCall], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==1
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if all(isinstance(arg, BVValue) for arg in args):
                return [BVValue(self.fun(args[0].value))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

def create_BVUnary(class_name: str, fun):
    cls = BVUnary
    cls.__name__ = "BV"+class_name.capitalize()
    return cls(class_name, fun)

class BVMux(CombPrimitive):
    name = QSym('bv', "mux")
    param_types = [IntType()]
    num_inputs = 3
    num_outputs = 1
    comm_info = ([0],[1],[2])

    def get_type(self, N: Expr):
        BVCall_1 = TypeCall(BVType(), [IntValue(1)])
        BVCall_N = TypeCall(BVType(), [N])
        return [BVCall_N, BVCall_N, BVCall_1], [BVCall_N] 

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==3
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if all(isinstance(arg, BVValue) for arg in args):
                return [BVValue(args[2].value.ite(args[1].value, args[0].value))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

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

class BVBin(CombPrimitive):
    param_types = [IntType()]
    num_inputs = 2
    num_outputs = 1

    def __init__(self, class_name: str, fun, comm):
        self.name = QSym('bv', class_name)
        self.comm_info = ([0,1],) if comm else ([0], [1])
        self.fun = fun

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [BVCall, BVCall], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==2
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if all(isinstance(arg, BVValue) for arg in args):
                return [BVValue(self.fun(args[0].value, args[1].value))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

def create_BVBinary(class_name: str, fun, comm):
    cls= BVBin
    cls.__name__ = "BV"+class_name.capitalize()
    return cls(class_name, fun, comm)

class BVComp(CombPrimitive):
    param_types = [IntType()]
    num_inputs = 2
    num_outputs = 1

    def __init__(self, class_name:str, fun, comm):
        self.name = QSym('bv', class_name)
        self.comm_info = ([0,1],) if comm else ([0], [1])
        self.fun = fun

    def get_type(self, N: Expr):
        BVCall_N = TypeCall(BVType(), [N])
        BVCall_1 = TypeCall(BVType(), [IntValue(1)])
        return [BVCall_N, BVCall_N], [BVCall_1]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==2
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            if all(isinstance(arg, BVValue) for arg in args):
                bv0 = ht.SMTBitVector[1](0)
                bv1 = ht.SMTBitVector[1](1)
                v = self.fun(args[0].value, args[1].value)
                assert isinstance(v, ht.SMTBit)
                return [BVValue(v.ite(bv1, bv0))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

def create_BVComp(class_name: str, fun, comm):
    cls = BVComp
    cls.__name__ = "BV"+class_name.capitalize()
    return cls(class_name, fun, comm)

def add(x,y):
    return x + y
def sub(x,y):
    return x - y
def mul(x,y):
    return x * y
def and_(x,y):
    return x & y
def or_(x,y):
    return x | y
def xor(x,y):
    return x ^ y
def lshr(x,y):
    return ht.SMTBitVector.bvlshr(x,y)
def ashr(x,y):
    return ht.SMTBitVector.bvashr(x,y)
def shl(x,y):
    return x << y
def smax(x,y):
    return x.bvsgt(y).ite(x,y)
def smin(x,y):
    return x.bvslt(y).ite(x,y)
def umax(x,y):
    return x.bvugt(y).ite(x,y)
def umin(x,y):
    return x.bvult(y).ite(x,y)
def mult_middle(x,y):
    w = x.num_bits
    prod = x.sext(w) * y.sext(w)
    return prod[w//2: w + w//2]

_binops = dict(
    add=(add, True),
    sub=(sub, False),
    mul=(mul, True),
    and_=(and_, True),
    or_=(or_, True),
    xor=(xor, True),
    lshr=(lshr, False),
    ashr=(ashr, False),
    shl=(shl, False),
    smax=(smax, True),
    smin=(smin, True),
    umax=(umax, True),
    umin=(umin, True),
    mult_middle=(mult_middle, True)
)

def eq(x,y):
    return x == y
def neq(x,y):
    return ~(x == y)
def ult(x,y):
    return x.bvult(y)
def slt(x,y):
    return x.bvslt(y)
def ule(x,y):
    return x.bvule(y)
def sle(x,y):
    return x.bvsle(y)
def ugt(x,y):
    return x.bvugt(y)
def sgt(x,y):
    return x.bvsgt(y)
def uge(x,y):
    return x.bvuge(y)
def sge(x,y):
    return x.bvsge(y)
_cmpops = dict(
    eq=(eq, True),
    neq=(neq, True),
    ult=(ult, False),
    slt=(slt, False),
    ule=(ule, False),
    sle=(sle, False),
    ugt=(ugt, False),
    sgt=(sgt, False),
    uge=(uge, False),
    sge=(sge, False),
)

def identity(x):
    return x
def neg(x):
    return -x
def not_(x):
    return ~x
def abs(x):
    return x.bvsge(0).ite(x,-x)
_unary_ops = dict(
    identity=identity,
    neg=neg,
    not_=not_,
    abs=abs,
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
            def __call__(self, x: BV[o]) -> BV[h-l]:
                return x[l:h]
        return Slice
    return slice_fc

class BVSlice(CombPeak):
    name = QSym("bv", "slice")
    def __init__(self):
        super().__init__(slice_peak, 3, lambda o, l, h : (o, h-l))

class BVNFlag(CombPrimitive):
    name = QSym('bv', 'nflag')
    param_types = [IntType()]
    comm_info = ([0], [1])
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
                x = args[0].value
                y = args[1].value
                n = (x-y)[-1]
                bv0 = ht.SMTBitVector[N.value](0)
                bv1 = ht.SMTBitVector[N.value](1)
                return [BVValue(n.ite(bv1, bv0))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])

class BVVFlag(CombPrimitive):
    name = QSym('bv', 'vflag')
    param_types = [IntType()]
    comm_info = ([0], [1])
    num_inputs = 2
    num_outputs = 1

    def get_type(self, N: Expr):
        BVCall = TypeCall(BVType(), [N])
        return [BVCall, BVCall], [BVCall]

    def eval(self, *args, pargs):
        assert len(pargs)==1 and len(args)==2
        N = pargs[0]
        if isinstance(N, IntValue) and isinstance(N.value, int):
            n = N.value
            if all(isinstance(arg, BVValue) for arg in args):
                x = args[0].value
                y = args[1].value
                a = (x-y).bvsge(0)
                b = (x.bvsge(y))
                v = (a^b)
                #v = (x.bvsgt(y) & (x-y)[-1]) | (x.bvsle(y) & ~(x-y)[-1])

                #xy = x.sext(1)-y.sext(1)
                #v = xy.slt(-(2**(n-1))) | xy.sge(2**(n-1))
                bv0 = ht.SMTBitVector[N.value](0)
                bv1 = ht.SMTBitVector[N.value](1)
                return [BVValue(v.ite(bv1, bv0))]
        return CallExpr(self, pargs, args)

    def partial_eval(self, N):
        return CombSpecialized(self, [N])



class BitVectorModule(Module):
    # Types
    def __init__(self):
        super().__init__('bv')
        opdict = dict(
            const=BVConst(),
            c_const=CBVConst(),
            _synth_const=CBVSynthConst(),
            abs_const=AbsConst(),
            dont_care=BVDontCare(),
            c_dont_care=CBVDontCare(),
            concat=BVConcat(),
            slice=BVSlice(),
            nflag=BVNFlag(),
            vflag=BVVFlag(),
            mux=BVMux()
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
