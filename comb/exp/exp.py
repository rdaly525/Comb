import hwtypes as ht
#Enumerate the instruction
from peak import Peak
import typing as tp

from hwtypes.adt import Tuple, Enum, Sum, TaggedUnion

from comb.frontend.ir import _flat


class ADTEnum:
    def __init__(self, adt, constructor: tp.Callable, immTs=[]):
        self.adt = adt
        self.constructor = constructor
        self.immTs = immTs

    @property
    def num_imms(self):
        return len(self.immTs)

    def __call__(self, *args):
        assert len(args) == len(self.immTs)
        assert all(isinstance(arg, immT) for arg, immT in zip(args, self.immTs))
        adt_val = self.constructor(*args)
        assert isinstance(adt_val, self.adt)
        return adt_val

import itertools as it
def is_bv(adt):
    return issubclass(adt, (ht.BitVector, ht.Bit))

def enumerate_adt(adt):
    if is_bv(adt):
        return [ADTEnum(adt, lambda x: x, [adt])]
    elif issubclass(adt, Enum):
        return [ADTEnum(adt, lambda : val) for val in adt.enumerate()]
    elif issubclass(adt, Tuple): #Tuple, Product
        adt_enumss = [enumerate_adt(T) for T in adt.fields]
        rets = []
        for adt_enums in it.product(*adt_enumss):
            imm_locs = [0] + list(it.accumulate([E.num_imms for E in adt_enums]))
            immTs = _flat(E.immTs for E in adt_enums)
            def constructor(*args):
                arg_list = [args[l:h] for l,h in zip(imm_locs[:-1], imm_locs[1:])]
                assert len(arg_list) == len(adt_enums)
                adt_args = [E(*arg) for E, arg in zip(adt_enums, arg_list)]
                return adt(*adt_args)
            rets.append(ADTEnum(adt, constructor, immTs))
        return rets
    elif issubclass(adt, TaggedUnion):
        adt_enumss = {k:enumerate_adt(T) for k, T in adt.field_dict.items()}
        rets = []
        for k, adt_enums in adt_enumss.items():
            for adt_enum in adt_enums:
                def constructor(*args):
                    return adt(**{k:adt_enum(*args)})
                rets.append(ADTEnum(adt, constructor, adt_enum.immTs))
        return rets
    elif issubclass(adt, Sum):
        adt_enumss = [enumerate_adt(T) for T in adt.fields]
        rets = []
        for adt_enums in adt_enumss:
            for adt_enum in adt_enums:
                def constructor(*args):
                    return adt(adt_enum(*args))
                rets.append(ADTEnum(adt, constructor, adt_enum.immTs))
        return rets
    else:
        raise NotImplementedError()


def enumerate_peak(pe: Peak) -> tp.Iterable[Peak]:
    iT = pe.input_t
    return [iT]

