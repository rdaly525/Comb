import hwtypes as ht
from comb.frontend.ast import QSym
from comb.frontend.comb_peak import CombPeak
from comb.frontend.ir import CombSpecialized
from comb.frontend.stdlib import CBVSynthConst
from comb.synth.comm_synth import set_comm
from comb.synth.solver_utils import SolverOpts
# from hwtypes.adt import Enum, Product
import hwtypes.smt_utils as fc
from peak.family import PyFamily, SMTFamily
from lassen.alu import ALU_t, Signed_t
from lassen.cond import Cond_t
from lassen.common import Global
from lassen.isa import Inst_fc
from lassen.lut import LUT_t_fc
from lassen.mode import gen_register_mode, gen_bit_mode, Mode_t
from lassen.sim import PE_fc
from peak import family_closure, Peak, Const
from peak.assembler import AssembledADT, Assembler

DATAWIDTH=4

solver_opts = SolverOpts(verbose=0, solver_name='bitwuzla', timeout=2000, log=False)
def parameterize_pe():
    @family_closure
    def ExpandedPE_fc(family):
        Bit = family.BitVector[1]
        Data = family.BitVector[DATAWIDTH]
        PE = PE_fc(family)
        Inst = Inst_fc(family)
        instc = family.get_constructor(Inst)
        LUT_t, _ = LUT_t_fc(family)

        @family.assemble(locals(), globals())
        class ExpandedPE(Peak):
            def __init__(self):
                self.PE = PE()

            def __call__(
                self,
                # const instruction inputs
                inst_op: ALU_t,
                inst_signed: Signed_t,
                inst_lut: LUT_t,
                inst_cond: Cond_t,
                inst_rega: Mode_t,
                inst_data0: Data,
                inst_regb: Mode_t,
                inst_data1: Data,
                inst_regc: Mode_t,
                inst_data2: Data,
                inst_regd: Mode_t,
                inst_bit0: Bit,
                inst_rege: Mode_t,
                inst_bit1: Bit,
                inst_regf: Mode_t,
                inst_bit2: Bit,
                # data inputs
                data0: Data,
                data1: Data,
                data2: Data,
                bit0: Bit,
                bit1: Bit,
                bit2: Bit,
                clk_en: Global(Bit),
            ) -> (Data, Bit):
                #inst_op = opc(alu = inst_op)

                inst_bit0 = inst_bit0[0]
                inst_bit1 = inst_bit1[0]
                inst_bit2 = inst_bit2[0]
                bit0 = bit0[0]
                bit1 = bit1[0]
                bit2 = bit2[0]
                clk_en = clk_en[0]

                inst = instc(inst_op, 
                             inst_signed,
                             inst_lut,
                             inst_cond,
                             inst_rega,
                             inst_data0,
                             inst_regb,
                             inst_data1,
                             inst_regc,
                             inst_data2,
                             inst_regd,
                             inst_bit0,
                             inst_rege,
                             inst_bit1,
                             inst_regf,
                             inst_bit2
                             )

                res, cond, _, _, _ =  self.PE(inst, data0, data1, data2, bit0, bit1, bit2, clk_en)
                return Data(res), Bit(cond)
            
        return ExpandedPE
    
    return ExpandedPE_fc


class CombPE(CombPeak):
    name = QSym("peak", "PE")
    def __init__(self):

        def type_gen():
            OPWIDTH = 5
            SIGNEDWIDTH = 1
            LUTWIDTH = 8
            CONDWIDTH = 5
            MODEWIDTH = 2
            return ( 
                (
                    #const instructions
                    OPWIDTH, 
                    SIGNEDWIDTH, 
                    LUTWIDTH,
                    CONDWIDTH,
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, DATAWIDTH, 
                    MODEWIDTH, 1, 
                    MODEWIDTH, 1, 
                    MODEWIDTH, 1, 
                    #data inputs
                    DATAWIDTH, DATAWIDTH, DATAWIDTH, 
                    1, 1, 1,
                    1
                ),
                (DATAWIDTH, 1)
            )

        consts = (
            (True,) * 16 + (False,) * 7,
            (False, False)
        )

        super().__init__(parameterize_pe, 0, type_gen, consts)
        set_comm(self, solver_opts)

def CombPE_constraints(in_lvars, out_lvars, in_vars, out_vars):
    cond = []
    family = SMTFamily()
    Inst = Inst_fc(family)
    instc = family.get_constructor(Inst)
    def convert_bit(b):
        assert isinstance(b, family.BitVector)
        if b.num_bits == 1:
            return b[0]
        return b

    inst_in_vars = tuple(in_vars[0:2]) +  tuple(convert_bit(b) for b in in_vars[2:16])
    inst = instc(*inst_in_vars)
    cond.append(type(inst)._is_valid_(inst._value_))
    cond.append(fc.And([inst_in_vars[i] != Mode_t.DELAY._value_ for i in [4,6,8,10,12,14]]).to_hwtypes())
    return fc.And(cond).to_hwtypes()

combPE = CombPE()[()]
combPE.constraints = CombPE_constraints

