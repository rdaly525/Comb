from . import Comb
from .synth import PatternSynth, get_var
import hwtypes as ht
import hwtypes.smt_utils as fc
# Create an adjacency graph
from .utils import comb_type_to_sT
import itertools as it

class DagSynth(PatternSynth):
    def __init__(self, *args):
        super().__init__(*args)
        if len(self.const_list) > 0:
            raise NotImplementedError()
        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")
        iTs, oTs = self.comb_type

        # Structure
        input_vars = [get_var(f"{self.prefix}_V_In{i}", T) for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        #const_vars = []
        output_vars = [get_var(f"{self.prefix}_V_Out{i}", T) for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{self.prefix}_V_Op[{opi}]_in[{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{self.prefix}_V_Op[{opi}]_out[{i}]", T) for i, T in enumerate(op_oTs)])

        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)

        # I need to create a bit for each possible input connection
        #Structure:
        #In: Inputs: [0, 1, 2 ...]
        #Out: Outputs: [0, 1, 2, ...]
        #opI: Ops: [0, 1, ...]
        #  SRC        ->  SNK
        # (kind, idx) -> (kind, idx)
        #
        input_T = comb_type_to_sT(iTs)
        output_T = comb_type_to_sT(oTs)
        op_iTs = [comb_type_to_sT(op.get_type()[0]) for op in self.op_list]
        op_oTs = [comb_type_to_sT(op.get_type()[1]) for op in self.op_list]

        # Create a set of all sources/snks sorted by type
        srcs = {n: [("In", i) for i in ids] for n, ids in input_T.items()}
        for opi, op_oT in enumerate(op_oTs):
            for n, ids in op_oT.items():
                srcs.setdefault(n, []).extend((opi, i) for i in ids)
        snks = {n: [("Out", i) for i in ids] for n, ids in output_T.items()}
        for opi, op_iT in enumerate(op_iTs):
            for n, ids in op_iT.items():
                snks.setdefault(n, []).extend((opi, i) for i in ids)

        snk_list = []
        src_poss = []
        for n, n_snks in snks.items():
            snk_list += n_snks
            src_poss += [srcs[n] for _ in n_snks]

        def invalid_edge(src, snk):
            return ((src[0] == snk[0])) or ((src[0], snk[0]) == ("In", "Out"))

        def invalid_edges(src_list):
            return any(invalid_edge(src, snk) for src, snk in zip(src_list, snk_list))

        edges = {}
        for src_list in it.product(*src_poss):
            if not invalid_edges(src_list):
                for src, snk in zip(src_list, snk_list):
                    edges[(src, snk)] = get_var(f"{src}->{snk}", 0)
        for e, ev in edges.items():
            print(e, ev)

        #get list of lvars (existentially quantified in final query)
        self.E_vars = ()

        And = fc.And
        #Lib Spec (P_lib)
        #   temp_var[i] = OP(*op_in_vars[i])
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(op_out_vars[i][j] == op_out_var)


        #Well formed program (P_wfp)
        flat_op_out_lvars = flat(op_out_lvars)

        # Temp locs and output locs are in range of temps
        P_in_range = []
        for lvar in flat_op_out_lvars:
            P_in_range.append(And([lvar>=Ninputs+Nconsts, lvar < tot_locs]))

        #op in locs and outputs are in range(0,tot)

        for lvar in self.rhs_lvars:
            P_in_range.append(lvar < tot_locs)

        #Ints are >= 0
        #BitVectors do not need this check
        if lvar_t is ht.SMTInt:
            for lvars in (
                    output_lvars,
                    flat(op_out_lvars),
                    flat(op_in_lvars),
            ):
                for lvar in lvars:
                    assert isinstance(lvar, lvar_t)
                    P_in_range.append(lvar >= 0)

        #TODO flag?
        #output loc cannot be inputs
        #for lvar in output_lvars:
        #    P_in_range.append(lvar >= Ninputs+Nconsts)

        # Temp locs are unique
        #Could simplify to only the first lhs of each stmt
        P_loc_unique = []
        for i in range(len(flat_op_out_lvars)):
            for j in range(i+1, len(flat_op_out_lvars)):
                P_loc_unique.append(flat_op_out_lvars[i] != flat_op_out_lvars[j])

        # multi outputs are off by 1
        P_multi_out = []
        for lvars in op_out_lvars:
            for lv0, lv1 in zip(lvars, lvars[1:]):
                P_multi_out.append(lv0+1==lv1)

        P_acyc = []
        # ACYC Constraint
        #  op_out_lvars[i] > op_in_lvars[i]
        for o_lvars, i_lvars in zip(op_out_lvars, op_in_lvars):
            P_acyc += [o_lvars[0] > ilvar for ilvar in i_lvars]

        #Same operations have a strict order
        op_to_i = {}
        for i, op in enumerate(self.op_list):
            op_to_i.setdefault(op.qualified_name, []).append(i)

        P_same_op = []
        for op, ilist in op_to_i.items():
            if len(ilist) > 1:
                for i, j in zip(ilist[:-1], ilist[1:]):
                    assert i < j
                    P_same_op.append(op_out_lvars[i][0] < op_out_lvars[j][0])

        #Strict ordering on arguments of commutative ops
        P_comm = []
        #TODO Re-enable
        for i, op in enumerate(self.op_list):
            if op.commutative:
                for lv0, lv1 in  zip(op_in_lvars[i][:-1], op_in_lvars[i][1:]):
                    P_comm.append(lv0 <= lv1)

        def rhss():
            for lvar in flat(op_in_lvars):
                yield lvar
            for lvar in output_lvars:
                yield lvar

        #All vars are used
        used = lvar_t(0)
        for lvar_rhs in rhss():
            used |= (lvar_t(1) << lvar_rhs)
        P_used = (used == (2**tot_locs)-1)

        P_wfp = [
            And(P_in_range),
            And(P_loc_unique),
            And(P_multi_out),
            And(P_acyc),
            And(P_same_op),
            And(P_comm),
            P_used,
        ]

        #Locations correspond to vars (P_conn)
        # (Lx == Ly) => (X==Y)
        pairs = []
        for lvars, vars in (
            (input_lvars, input_vars),
            (output_lvars, output_vars),
            (hard_const_lvars, hard_consts),
            (flat(op_out_lvars), flat(op_out_vars)),
            (flat(op_in_lvars), flat(op_in_vars)),
        ):
            for lvar, var in zip(lvars, vars):
                pairs.append((lvar, var))
        P_conn = []
        for i in range(len(pairs)):
            for j in range(i+1, len(pairs)):
                lv0, v0 = pairs[i]
                lv1, v1 = pairs[j]
                #Types need to match
                #Type is allowed to be an int
                if type(v0) != type(v1) and not isinstance(v0, int) and  not isinstance(v1, int):
                    continue
                #skip if both loc vars are int
                if isinstance(lv0, int) and isinstance(lv1, int):
                    continue
                P_conn.append(fc.Implies(lv0==lv1, v0==v1))

        self.P_wfp = And(P_wfp)
        self.P_lib = And(P_lib)
        self.P_conn = And(P_conn)

