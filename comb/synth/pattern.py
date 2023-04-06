from collections import namedtuple
from functools import cache, cached_property
import networkx as nx
import hwtypes.smt_utils as fc
from dataclasses import dataclass
from ..frontend.ast import Comb, Type, Sym, QSym, InDecl, OutDecl
import typing as tp

from .solver_utils import get_var
from .utils import _make_list, type_to_N, _list_to_dict, N_to_type
from ..frontend.ir import CombProgram, AssignStmt
import itertools as it

#Represnts the raw dag structure of a particular pattern
#Inputs are encoded as -1
#Outputs are encoded as num_ops

SymOpts = namedtuple('SymOpts', ('comm', 'same_op', 'input_perm'), defaults=(False,)*3)

#(canonicalize comm=True means allow ckecing comm
#(canonicalize same ops means
def matcher(from_pat, from_root, to_pat, to_root, opts: SymOpts):
    r = from_pat
    r_root = from_root
    l = to_pat
    l_root = to_root
    def match(l_src, r_src, ctx):
        l_opi, l_arg = l_src
        r_opi, r_arg = r_src
        #Check if already done or if mismatch

        #TODO base case for (-1)
        if r_opi == -1:
            ctx = {r_src: l_src, **ctx}
            return ctx
        if l_arg != r_arg:
            return None

        if r_opi in ctx:
            if ctx[r_opi]==l_opi:
                return ctx
            else:
                return None

        if opts.same_op:
            if l.op_names[l_opi] != r.op_names[r_opi]:
                return None
        else:
            if l_opi != r_opi:
                return None
        l_nodes = [l.nodes[l_opi]]
        #TODO only works for comm size 2
        if opts.comm and l_opi in range(l.num_ops) and l.ops[l_opi].commutative:
            l_nodes.append(reversed(l.nodes[l_opi]))

        succ_ctx = None
        for l_node in l_nodes:
            cur_succ = True
            ctx_ = {**ctx}
            for l_src, r_src in zip(l_node, r.nodes[r_opi]):
                #Out index must be the same
                match_ctx = match(l_src, r_src, ctx)
                if match_ctx is None:
                    cur_succ = False
                    break
                ctx_ = {**match_ctx, **ctx_}
            if cur_succ:
                succ_ctx = ctx_
                break
        if succ_ctx is None:
            return None

        ctx = {r_opi:l_opi, **ctx_}
        return ctx
    return match(l_root, r_root, {})

class Pattern:
    def __init__(self, iT, oT, ops: tp.List[Comb]):
        assert all(n >=0 for n in iT)
        assert all(n >=0 for n in oT)
        if len(oT) > 1:
            raise NotImplementedError()
        self.iT = iT
        self.oT = oT
        self.ops = ops
        self.node_range = range(-1, len(ops)+1)
        self.edges = []
        self.op_iTs = []
        self.op_oTs = []
        for op in ops:
            iT, oT = op.get_type()
            self.op_iTs.append([type_to_N(t) for t in iT])
            self.op_oTs.append([type_to_N(t) for t in oT])
        self.nodes = {**{i:[None for _ in self.op_iTs[i]] for i in range(len(ops))}, len(ops):[None for _ in oT]}
        self.root = (len(ops), 0) #TODO only works for single output

    @cached_property
    def op_names(self):
        return [op.qualified_name for op in self.ops] + ["IO"]

    @cached_property
    def num_ops(self):
        return len(self.ops)

    def add_edge(self, src, snk):
        assert len(src)==2 and len(snk)==2
        assert src[0] in self.node_range
        assert snk[0] in self.node_range
        if src[0] == -1:
            src_t = self.iT[src[1]]
        else:
            src_t = self.op_oTs[src[0]][src[1]]

        if snk[0] == self.num_ops:
            snk_t = self.oT[snk[1]]
        else:
            snk_t = self.op_iTs[snk[0]][snk[1]]
        assert src_t == snk_t
        self.edges.append((src, snk))
        self.nodes[snk[0]][snk[1]] = src

    #@property
    #def interior_edges(self):
    #    yield from (e for e in self.edges if all(v in range(self.num_ops) for v in (e[0][0], e[1][0])))

    #@property
    #def in_edges(self):
    #    yield from (e for e in self.edges if e[0][0]==-1)

    #@property
    #def out_edges(self):
    #    yield from (e for e in self.edges if e[1][0]==self.num_ops)

    @cached_property
    def op_dict(self):
        return _list_to_dict(self.op_names)

    def equal(self, other, opts: SymOpts):
        if not isinstance(other, Pattern):
            return False
        if (self.iT, self.oT, self.op_names) != (other.iT, other.oT, other.op_names):
            return False
        matches = matcher(other, other.root, self, self.root, opts)
        if matches is None:
            return False
        if opts.input_perm:
            inputs = [(-1, i) for i in range(len(self.iT))]
            matched_inputs = (matches[input] for input in inputs)
            return set(inputs) == set(matched_inputs)
        else:
            return all((-1, i)==matches[(-1,i)] for i in range(len(self.iT)))


    def __str__(self):
        ret = ",".join([f"{i}:{op}" for i, op in enumerate(self.op_names)]) + "\n  "
        return ret + "\n  ".join(f"{l} -> {r}" for l,r in self.edges)

    def __hash__(self):
        return hash(str(self))

    #TODO verify this works
    def to_comb(self, ns, name) -> CombProgram:

        #Create symbol mapping
        src_to_sym = {(-1,i): Sym(f"I{i}") for i in range(len(self.iT))}
        for opi in range(self.num_ops):
            src_to_sym.update({(opi, i):Sym(f"t{opi}_{i}") for i in range(len(self.op_oTs[opi]))})

        snk_to_sym = {}
        for src, snk in self.edges:
            assert src in src_to_sym
            snk_to_sym[snk] = src_to_sym[src]
        src_to_sym.update({(self.num_ops, i): Sym(f"O{i}") for i in range(len(self.oT))})

        inDecls = [InDecl(src_to_sym[(-1,i)], N_to_type(n)) for i, n in enumerate(self.iT)]
        outDecls = [OutDecl(src_to_sym[(self.num_ops, i)], N_to_type(n)) for i, n in enumerate(self.oT)]

        opi_to_assign = {}
        for opi, op in enumerate(self.ops):
            lhss = [src_to_sym[(opi, i)] for i in range(len(self.op_oTs[opi]))]
            args = [snk_to_sym[(opi, i)] for i in range(len(self.op_iTs[opi]))]
            opi_to_assign[opi] = AssignStmt(lhss, [op.call_expr([], args)])
        #Create output decl O0, O1 = t0_1, t2_2
        out_lhs = [src_to_sym[(self.num_ops, i)] for i in range(len(self.oT))]
        out_rhs = [snk_to_sym[(self.num_ops, i)] for i in range(len(self.oT))]
        out_assign = AssignStmt(out_lhs, out_rhs)

        g = nx.DiGraph()
        for (src, _), (snk, _) in self.edges:
            g.add_edge(src, snk)
        order = list(nx.topological_sort(g))

        #Could be a constant
        #Remove inputs from order
        order = [i for i in order if i !=-1]
        assert order[-1] == self.num_ops
        opAssigns = [opi_to_assign[opi] for opi in order[:-1]]
        stmts = [*inDecls, *outDecls, *opAssigns, out_assign]
        comb = CombProgram(QSym(ns, name), stmts)
        return comb



class PatternEncoding:
    def __init__(
        self,
        iT: tp.List[int],
        oT: tp.List[int],
        op_list: tp.List[Comb],
        const_list: tp.Tuple[int] = (),
        prefix: str = "",
        sym_opts: SymOpts = SymOpts(),
    ):
        self.iT = iT
        self.oT = oT
        self.op_list = op_list
        self.const_list = const_list
        self.prefix = prefix
        self.sym_opts = sym_opts

        if len(self.const_list) > 0:
            raise NotImplementedError()
        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")

        # Structure
        input_vars = [get_var(f"{prefix}_In[{i}]", n) for i, n in enumerate(iT)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        output_vars = [get_var(f"{prefix}_Out[{i}]", n) for i, n in enumerate(oT)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        for opi, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_iTs, op_oTs = op.get_type()
            op_in_vars.append([get_var(f"{prefix}_OpIn[{opi}][{i}]", T) for i, T in enumerate(op_iTs)])
            op_out_vars.append([get_var(f"{prefix}_OpOut[{opi}][{i}]", T) for i, T in enumerate(op_oTs)])
        self.input_vars = input_vars
        self.output_vars = output_vars
        self.op_out_vars = op_out_vars
        self.op_in_vars = op_in_vars
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)

    @property
    def P_lib(self):
        P_lib = []
        for i, op in enumerate(self.op_list):
            ovars = _make_list(op.evaluate(*self.op_in_vars[i]))
            for j, op_out_var in enumerate(ovars):
                P_lib.append(self.op_out_vars[i][j] == op_out_var)
        return fc.And(P_lib)

    @property
    def P_conn(self):
        raise NotImplementedError()

    @property
    def P_wfp(self):
        raise NotImplementedError()

    @property
    def P_sym_same_op(self):
        raise NotImplementedError()

    @property
    def P_sym_comm(self):
        raise NotImplementedError()

    @property
    def P_sym_input_perm(self):
        raise NotImplementedError()

    @property
    def P_sym(self):
        P_sym = []
        if self.sym_opts.comm:
            P_sym.append(self.P_sym_comm)
        if self.sym_opts.same_op:
            P_sym.append(self.P_sym_same_op)
        if self.sym_opts.input_perm:
            P_sym.append(self.P_sym_input_perm)
        return fc.And(P_sym)

    @cached_property
    def num_ops(self):
        return len(self.op_list)

    def pattern_from_sol(self, sol):
        raise NotImplementedError()

    #Makes sure the typing makes sense for the query
    def types_viable(self):
        raise NotImplementedError()
        def cnt_vals(vals):
            cnt = collections.defaultdict(int)
            for v in vals:
                cnt[v] += 1
            return cnt

        spec_iTs, spec_oTs = self.comb_type
        spec_inputs = cnt_vals(i.type for i in spec_iTs)
        spec_outputs = cnt_vals(o.type for o in spec_oTs)

        op_inputs = cnt_vals(flat([[i.type for i in op.get_type()[0]] for op in self.op_list]))
        op_outputs = cnt_vals(flat([[o.type for o in op.get_type()[1]] for op in self.op_list]))

        if not all(t in op_inputs and op_inputs[t] >= cnt for t, cnt in spec_inputs.items()):
            return False
        if not all(t in op_outputs and op_outputs[t] >= cnt for t, cnt in spec_outputs.items()):
            return False
        return True
