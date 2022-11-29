from .ir import CombPrimitive

class CombPeak(CombPrimitive):
    param_types = []
    def __init__(self, peak_fc):
        self.peak_smt = peak_fc.SMT()
        #TODO figure out inputs and output types

    def eval(self, *args, pargs=[]):
        assert len(pargs)==0
        raise NotImplementedError()
