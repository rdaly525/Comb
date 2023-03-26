
from .pattern import PatternEncoding
from .solver_utils import get_var
import hwtypes as ht
import hwtypes.smt_utils as fc
# Create an adjacency graph
from .utils import comb_type_to_sT, _make_list, flat, _list_to_dict
import itertools as it

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


def p(x):
    n = len(x)
    print()
    for ni, nj in it.product(range(n), range(n)):
        print(f"({ni},{nj}): {str(x[ni][nj].value)}")
    #print("\n".join([f"{i}: {x[i][i].value.simplify()}" for i in range(n)]))
    #print("\n".join([" ".join([str(v.value) for v in vs]) for vs in x]))


def simp(v):
    return type(v)(v.value.simplify())

#This is the adjacency encoding
class AdjEncoding(PatternEncoding):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

        #Structure:
        #In (-1): Inputs: [0, 1, 2 ...]
        #Out (numOps): Outputs: [0, 1, 2, ...]
        #opI: Ops: [0, 1, ...]
        #  SRC        ->  SNK
        # (kind, idx) -> (kind, idx)
        num_ops = len(self.op_list)
        self.num_ops = num_ops
        iTs, oTs = self.comb_type
        input_T = comb_type_to_sT(iTs)
        output_T = comb_type_to_sT(oTs)
        op_iTs = [comb_type_to_sT(op.get_type()[0]) for op in self.op_list]
        op_oTs = [comb_type_to_sT(op.get_type()[1]) for op in self.op_list]

        # Create a set of all sources/snks sorted by type
        srcs = {n: [(-1, i) for i in ids] for n, ids in input_T.items()}
        for opi, op_oT in enumerate(op_oTs):
            for n, ids in op_oT.items():
                srcs.setdefault(n, []).extend((opi, i) for i in ids)
        snks = {n: [(num_ops, i) for i in ids] for n, ids in output_T.items()}
        for opi, op_iT in enumerate(op_iTs):
            for n, ids in op_iT.items():
                snks.setdefault(n, []).extend((opi, i) for i in ids)
        self.srcs = srcs
        self.snks = snks
        snk_list = []
        src_poss = []
        for n, n_snks in snks.items():
            snk_list += n_snks
            src_poss += [srcs[n] for _ in n_snks]


        idx_to_op = {i:op.qualified_name for i, op in enumerate(self.op_list)}
        idx_to_op.update({-1:'In', self.num_ops:'Out'})

        #Invalid edges are non-type matched
        # source and destination are same op
        # if same_op is enabled, then any edge from a later source to an earlier sink is invalid
        def invalid_edge(src_i, snk_i):
            if src_i == snk_i:
                return True
            if src_i == -1 and snk_i == num_ops:
                return True
            if self.sym_opts.same_op:
                if idx_to_op[src_i] == idx_to_op[snk_i]:
                    return src_i >= snk_i
            return False


        def kind_name(v):
            if v==-1:
                return 'In'
            if v== num_ops:
                return 'Out'
            return f"Op{v}"

        edges = {}
        for n, n_snks in snks.items():
            for snk in n_snks:
                for src in srcs[n]:
                    if not invalid_edge(src[0], snk[0]):
                        vname = f"({kind_name(src[0])},{src[1]})->({kind_name(snk[0])},{snk[1]})"
                        edges[(src, snk)] = get_var(vname, 0)

        self.edges = edges
        print("\nNE", len(self.edges))
        for e, ev in edges.items():
            print(e, str(ev.value))

    @property
    def E_vars(self):
        #get list of lvars (existentially quantified in final query)
        return list(self.edges.values())

    def _edges_from_src(self, src):
        return {snk:lv for (src_i, snk), lv in self.edges.items() if src_i == src}

    def _edges_from_snk(self, snk):
        return {src:lv for (src, snk_i), lv in self.edges.items() if snk_i == snk}

    @property
    def P_conn(self):
        def get_v_var(node, src=True):
            kind, idx = node
            if kind < 0:
                return self.input_vars[idx]
            elif kind >= self.num_ops:
                return self.output_vars[idx]
            elif src:
                return self.op_out_vars[kind][idx]
            else:
                return self.op_in_vars[kind][idx]

        #Connection constraints
        P_conn = []
        for (src_node, snk_node), v_pred in self.edges.items():
            src_v = get_v_var(src_node, src=True)
            snk_v = get_v_var(snk_node, src=False)
            P_conn.append(fc.Implies(v_pred, src_v==snk_v))
        return fc.And(P_conn)

    @property
    def P_unique_sink(self):
        #Snks have exactly one source
        P_unique_sink = []
        for n, snk_list in self.snks.items():
            for snk in snk_list:
                vs = [v for (_, snk_i), v in self.edges.items() if snk==snk_i]
                P_unique_sink.append(exactly_one(*vs))
        return fc.And(P_unique_sink)

    @property
    def P_used_source(self):
        #Make sure sources have more than 0 sinks
        #either op output can be used. (one can be unused iff the other is used)
        P_used_source = []
        for opi, op in enumerate(self.op_list):
            op_out_vs = []
            for i in range(op.num_outputs):
                vs = [v for (e_src, e_snk), v in self.edges.items() if e_src==(opi, i)]
                op_out_vs.extend(vs)
            P_used_source.append(fc.Or(op_out_vs))
        for src in ((-1, i) for i, _ in enumerate(self.input_vars)):
            vs = [v for (e_src, e_snk), v in self.edges.items() if e_src==src]
            P_used_source.append(fc.Or(vs))
        return fc.And(P_used_source)

    @property
    def P_acyc(self):
        #Premature optimizations:
        #   Unify each source input as the 'or' of each input term
        #   0 out the full diagonal after every Iteration
        #   only check even iterations
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
        nodes = []
        #adj[src][snk]
        adj = [[None for _ in self.op_list] for _ in self.op_list]
        for src_i, src_op in enumerate(self.op_list):
            for snk_i, snk_op in enumerate(self.op_list):
                vs = [v for ((_src_i, _), (_snk_i, _)), v in self.edges.items() if (src_i==_src_i and snk_i==_snk_i)]
                adj[src_i][snk_i] = fc.Or(vs).to_hwtypes()

        p(adj)
        terms = []
        def exp(x, n):
            if n == 1:
                return x
            else:
                x_nm1 = exp(x, n-1)
                x_n = matmul(x_nm1, x)
                terms.append(fc.And([~simp(x_n[i][i]) for i in range(self.num_ops)]))
                for i in range(self.num_ops):
                    #This is fine because I am asserting that eacbh x_n[i][i] is false
                    x_n[i][i] = ht.SMTBit(0)
                return x_n

        exp(adj, len(self.op_list))

        #I only need to check the op outputs (As all the op inputs will be in the cycle)
        ret = fc.And(terms)
        print(ret.serialize())
        return ret

    @property
    def P_wfp(self):
        wfp = [
            self.P_unique_sink,
            self.P_used_source,
            self.P_acyc,
        ]
        return fc.And(wfp)


    @property
    def P_sym_same_op(self):
        assert self.sym_opts.same_op
        #Tactic: for each same op, add a custom directed edge in the adj matrix
        #Add constraints that all edges from a later same op to an early same op is 0

        #P_op_order = []
        #idx_to_op = {i:op.qualified_name for i, op in enumerate(self.op_list)}
        #for (src, snk), v in self.edges.items():
        #    src_i = src[0]
        #    snk_i = snk[0]
        #    if not all(isinstance(i, int) for i in (src_i, snk_i)):
        #        continue
        #    if idx_to_op[src_i] != idx_to_op[snk_i]:
        #        continue
        #    if snk_i <= src_i:
        #        P_op_order.append(~v)
        return fc.And([])

    @property
    def P_sym_comm(self):
        assert self.sym_opts.comm
        #Tactic: All pairwise exclusions.
        comm_op_ids = []
        for i, op in enumerate(self.op_list):
            if op.commutative:
                comm_op_ids.append(i)
        def in_to_int(src):
            if src[0]=='In':
                return (-1, src[1])
            return src
        def gt(src_a, src_b):
            src_a = in_to_int(src_a)
            src_b = in_to_int(src_b)
            if src_a[0] == src_b[0]:
                return src_a[1] > src_b[1]
            return src_a[0] > src_b[0]

        P_comm = []
        for op_i in comm_op_ids:
            snk_l = (op_i, 0)
            snk_r = (op_i, 1)
            l_lvars = {src:lvar for (src, snk), lvar in self.edges.items() if snk==snk_l}
            r_lvars = {src:lvar for (src, snk), lvar in self.edges.items() if snk==snk_r}
            for (src_l, lv), (src_r, rv) in it.product(l_lvars.items(), r_lvars.items()):
                #if l > r, invalid
                if gt(src_l, src_r):
                    P_comm.append(~(lv & rv))

        return fc.And(P_comm)

    @property
    def P_sym_input_perm(self):
        assert self.sym_opts.input_perm
        iTs, oTs = self.comb_type
        input_T = comb_type_to_sT(iTs)

        # Create a set of all sources/snks sorted by type
        P_perms = []
        for n, ids in input_T.items():
            # in_lvars[in_idx][...]
            in_lvars = []
            for id in ids:
                in_lvars.append([lvar for (src, _), lvar in self.edges.items() if src==('In', id)])
            assert all(len(in_lvars[0]) == len(lvars) for lvars in in_lvars)

            P_perm = []
            used = [ht.SMTBit(0) for _ in in_lvars]
            for i in range(len(in_lvars[0])):
                lvars = [in_lvars[in_i][i] for in_i in range(len(ids))]
                assert len(used) == len(lvars)
                i_perm = []
                for ui, u in enumerate(used[:-1]):
                    i_perm.append(fc.Implies(~u, fc.And([~lvar for lvar in lvars[ui+1:]])))
                used = [u | lvars[ui] for ui, u in enumerate(used)]
                P_perm.append(fc.And(i_perm))
            P_perms.append(fc.And(P_perm))
        return fc.And(P_perms)

    def pattern_from_solved(self, sol):
        raise NotImplementedError()

    def comb_from_solved(self, sol, name):
        return None
        #raise NotImplementedError()
