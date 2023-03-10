import pysmt.shortcuts

from . import Comb
from .synth import PatternSynth, get_var
import hwtypes as ht
import hwtypes.smt_utils as fc
# Create an adjacency graph
from .utils import comb_type_to_sT, _make_list, flat, _list_to_dict
import itertools as it

#Very similar to Buchwald:
#   Instead of using a straightline program to represent a graph I use an adjacency Matrix which literally represents the graph
#   #Each query has a set of inputs, a set of outputs, and a set of ops. Each op has inputs and outputs
#   #Each of these (inputs, outputs, op inputs, op outputs) are 'nodes' in the adjacency matrix
#   #The values of the matrix are filled so that it represents a directed connection between some source and sink node
#   #All that match the type and the 'source' and 'sink' have a boolean variable representing if it is connected or not
#   #For each op the outputs depend on the inputs.
#   Connection constraints are obvious. the adjacency matrix
import pysmt.shortcuts as smt

def exactly_one(*args):
    return ht.SMTBit(smt.ExactlyOne(*[arg.value for arg in args]))

def matmul(x, y):
    N = len(x)
    z = [[None for _ in range(N)] for _ in range(N)]
    for r in range(N):
        for c in range(N):
            z[r][c] = ht.SMTBit(0)
            for i in range(N):
                z[r][c] |= x[r][i] & y[i][c]
    return z

def mator(x, y):
    N = len(x)
    return [[x[r][c] | y[r][c] for c in range(N)] for r in range(N)]

def exp(x, n):
    if n == 1:
        return x, x
    else:
        x_nm1, x_or = exp(x, n-1)
        x_n = matmul(x_nm1, x)
        return x_n, mator(x_n, x_or)
        #return matmul(x, exp(x, n - 1))

def p(x):
    n = len(x)
    print()
    print("\n".join([f"{i}: {x[i][i].value.simplify()}" for i in range(n)]))
    print("\n".join([" ".join([str(v.value) for v in vs]) for vs in x]))



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
        input_vars = [get_var(f"{self.prefix}_In[{i}]", T) for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        #const_vars = []
        output_vars = [get_var(f"{self.prefix}_Out[{i}]", T) for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{self.prefix}_OpIn[{opi}][{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{self.prefix}_OpOut[{opi}][{i}]", T) for i, T in enumerate(op_oTs)])

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
                    vname = f"({src[0]},{src[1]})->({snk[0]},{snk[1]})"
                    edges[(src, snk)] = get_var(vname, 0)
        #for e, ev in edges.items():
        #    print(e, ev)

        #get list of lvars (existentially quantified in final query)
        self.E_vars = list(edges.values())


        And = fc.And

        #Lib Spec (P_lib)
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(op_out_vars[i][j] == op_out_var)


        def get_v_var(node, src=True):
            kind, idx = node
            if kind == "In":
                return input_vars[idx]
            elif kind == "Out":
                return output_vars[idx]
            elif src:
                return op_out_vars[kind][idx]
            else:
                return op_in_vars[kind][idx]

        #Connection constraints
        P_conn = []
        for (src_node, snk_node), v_pred in edges.items():
            src_v = get_v_var(src_node, src=True)
            snk_v = get_v_var(snk_node, src=False)
            P_conn.append(fc.Implies(v_pred, src_v==snk_v))

        #Well formed program (P_wfp)

        #Snks have exactly one source
        P_unique_sink = []
        for n, snk_list in snks.items():
            for snk in snk_list:
                vs = [v for (e_src, e_snk), v in edges.items() if e_snk==snk]
                P_unique_sink.append(exactly_one(*vs))

        #Srcs have more than 0 sinks
        #either op output can be used. (one can be unused iff the other is used)
        P_used_source = []
        for opi, op in enumerate(self.op_list):
            op_out_vs = []
            for i in range(op.num_outputs):
                vs = [v for (e_src, e_snk), v in edges.items() if e_src==(opi, i)]
                op_out_vs.extend(vs)
            P_used_source.append(fc.Or(op_out_vs))
        for src in (('In', i) for i, _ in enumerate(input_vars)):
            vs = [v for (e_src, e_snk), v in edges.items() if e_src==src]
            P_used_source.append(fc.Or(vs))

        #ACYC Constraint
        #First construct adjacency matrix A
        #ACYC iff each power of A has 0s on the digonal
        # op0_out0
        # op0_out1
        # op1_out0
        # op1_out1
        # op0_in0
        # op0_in1
        # ...
        op_outs = []
        op_ins = []
        for opi, op in enumerate(self.op_list):
            op_iTs, op_oTs = op.get_type()
            op_outs.extend((opi, i) for i, _ in enumerate(op_oTs))
            op_ins.extend((opi, i) for i, _ in enumerate(op_iTs))
        nodes = op_outs + op_ins
        Nout = len(op_outs)
        def get(src, snk, srci, snki):
            if (src, snk) in edges:
                return edges[(src, snk)]
            if (srci >= Nout) and (snki < Nout) and (src[0]==snk[0]):
                return ht.SMTBit(1)
            return ht.SMTBit(0)

        #Create the adjacency matrix
        adj = [[get(src, snk, srci, snki) for snki, snk in enumerate(nodes)] for srci, src in enumerate(nodes)]
        #Only need 2 times number of ops as that is the max path through all the ops
        _, adj_N = exp(adj, 2*len(self.op_list))

        P_acyc = [~(adj_N[i][i]) for i in range(Nout)]

        #Strict ordering of identical ops:
        #(currently) Only works when each op has only 1 output
        assert all(len(op.get_type()[1])==1 for op in self.op_list)
        op_dict = _list_to_dict([op.qualified_name for op in self.op_list])
        P_op_order = []
        for op, ids in op_dict.items():
            for id_i, src_i in enumerate(ids[:-1]):
                for snk_i in ids[id_i+1:]:
                    P_op_order.append(~adj_N[src_i][snk_i])
        P_wfp = [
            And(P_unique_sink),
            And(P_used_source),
            And(P_acyc),
            And(P_op_order),
        ]

        self.P_wfp = And(P_wfp)
        self.P_lib = And(P_lib)
        self.P_conn = And(P_conn)

