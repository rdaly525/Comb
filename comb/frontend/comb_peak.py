from .ast import IntType, Expr, TypeCall, BVType, CBVType, IntValue, BVValue
from .ir import CombPrimitive, CallExpr
from comb.synth.utils import _make_list


class CombPeak(CombPrimitive):
    def __init__(self, peak_gen, num_pargs, type_gen, consts = None):
        self.peak_gen = peak_gen
        self.param_types = [IntType() for _ in range(num_pargs)]
        self.type_gen = type_gen
        self.consts = consts

        #cache pargs -> peak_smt
        self.cache = {}

        #Calculate num inputs and outputs
        fake_args = [8 for _ in range(num_pargs)]
        i, o = type_gen(*fake_args)
        self.ni = len(_make_list(i))
        self.no = len(_make_list(o))

    @property
    def num_inputs(self) -> int:
        return self.ni

    @property
    def num_outputs(self) -> int:
        return self.no

    def get_type(self, *pargs):
        assert len(pargs) == len(self.param_types)
        assert all(isinstance(parg, Expr) for parg in pargs)
        iTs, oTs = self.type_gen(*pargs)
        iTs = _make_list(iTs)
        oTs = _make_list(oTs)
        iTs = [(IntValue(i) if isinstance(i, int) else i) for i in iTs]
        oTs = [(IntValue(o) if isinstance(o, int) else o) for o in oTs]
        assert all(isinstance(val, Expr) for val in iTs)
        assert all(isinstance(val, Expr) for val in oTs)
        if self.consts is not None:
            iconsts = _make_list(self.consts[0])
            oconsts = _make_list(self.consts[1])
        else:
            iconsts = [False for _ in iTs]
            oconsts = [False for _ in oTs]
        iTs = [TypeCall(CBVType() if const else BVType(), [val]) for val,const in zip(iTs, iconsts)]
        oTs = [TypeCall(CBVType() if const else BVType(), [val]) for val,const in zip(oTs, oconsts)]
        #TODO Verify that types match the generated peak_fc
        return iTs, oTs

    def eval(self, *args, pargs=[]):
        if not all(isinstance(p, IntValue) and isinstance(p.value, int) for p in pargs):
            return CallExpr(self, pargs, args)
        if not all(isinstance(arg, BVValue) for arg in args):
            return CallExpr(self, pargs, args)
        pargs = tuple(p.value for p in pargs)
        if pargs in self.cache:
            peak_smt = self.cache[pargs]
        else:
            peak_smt = self.peak_gen(*pargs).SMT()
            self.cache[pargs] = peak_smt
        raw_args = [arg.value for arg in args]
        rets = _make_list(peak_smt(*raw_args))
        return [BVValue(ret) for ret in rets]

