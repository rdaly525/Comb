import functools
from collections import namedtuple
from functools import cache, cached_property
import networkx as nx
import hwtypes.smt_utils as fc
from dataclasses import dataclass
from ..frontend.ast import Comb, Type, Sym, QSym, InDecl, OutDecl
import typing as tp

from .utils import _make_list, type_to_nT, _list_to_dict, nT_to_type, nT, _list_to_counts, types_to_nTs, add_cnts, \
    ge0_cnts, sub_cnts, types_to_nT_cnts, flat
from ..frontend.ir import CombProgram, AssignStmt
import itertools as it



class Program:
    def __init__(self, iT, oT, ops: tp.List[Comb]):
        assert all(T.n >=0 for T in iT)
        assert all(T.n >=0 for T in oT)
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
            self.op_iTs.append([type_to_nT(t) for t in iT])
            self.op_oTs.append([type_to_nT(t) for t in oT])
        self.nodes = {**{i:[None for _ in self.op_iTs[i]] for i in range(len(ops))}, len(ops):[None for _ in oT]}
        self.root = (len(ops), 0) #TODO only works for single output

    #Produces the maximum typing for these set of ops
    #@cached_property
    #def max_T(self):
    #    [_list_to_counts(iTs) for iTs in self.op_iTs]


    @cached_property
    def op_names(self):
        return [op.qualified_name for op in self.ops]

    @cached_property
    def op_names_with_io(self):
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
        if src_t != snk_t:
            raise ValueError()
            assert src_t == snk_t
        self.edges.append((src, snk))
        # snk, snk -> src
        self.nodes[snk[0]][snk[1]] = src

    @property
    def interior_edges(self):
        yield from (e for e in self.edges if all(v in range(self.num_ops) for v in (e[0][0], e[1][0])))

    @property
    def in_edges(self):
        yield from (e for e in self.edges if e[0][0]==-1)

    @property
    def out_edges(self):
        yield from (e for e in self.edges if e[1][0]==self.num_ops)

    @cached_property
    def op_dict(self):
        return _list_to_dict(self.op_names)

    @cached_property
    def op_cnt(self):
        return _list_to_counts(self.op_names)


    def enum_all_equal(self):
        #Does all the symmetries
        for es_ip in self.enum_input_perm(self.edges):
            for es_so, synth_vals in self.enum_same_op(es_ip):
                for es_c in self.enum_comm(es_so):
                    p = Pattern(self.iT, self.oT, self.ops, es_c, synth_vals)
                    yield p

    def enum_input_perm(self, edges):
        yield edges

    def enum_comm(self, edges):
        for op_poss in it.product(*[it.product(*[it.permutations(comm) for comm in op.comm_info]) for op in self.ops]):
            map = {self.num_ops:{0:0}} #[opi][ai]
            for opi, (op, poss) in enumerate(zip(self.ops, op_poss)):
                map[opi] = {f:t for f,t in zip(flat(self.ops[opi].comm_info), flat(poss))}
            es = []
            for src, (snk_i, snk_a) in edges:
                new_snk = (snk_i, map[snk_i][snk_a])
                es.append((src, new_snk))
            yield es

    def enum_same_op(self, edges):
        #First only do the comm_symmetries
        ops = self.op_dict.keys()
        self_ids = flat(self.op_dict.values())
        for ids in it.product(*[it.permutations(self.op_dict[op]) for op in ops]):
            op_map = {**{f:t for f,t in zip(self_ids, flat(ids))},-1:-1,self.num_ops:self.num_ops}
            es = []
            for (src_i, src_a), (snk_i, snk_a) in edges:
                new_src = (op_map[src_i], src_a)
                new_snk = (op_map[snk_i], snk_a)
                es.append((new_src, new_snk))
            yield es


    def equal(self, other, opts: SymOpts):
        matches = self.equal_with_match(other, opts)
        if opts.input_perm:
            raise NotImplementedError()
            inputs = [(-1, i) for i in range(len(self.iT))]
            matched_inputs = (matches[input] for input in inputs)
            return set(inputs) == set(matched_inputs)
        else:
            return any(all((-1, i)==match[(-1,i)] for i in range(len(self.iT))) for match in matches)

    #Returns if the patterns are equal and the input matches
    def equal_with_match(self, other: 'Pattern', opts: SymOpts):
        if not isinstance(other, Pattern):
            return []
        if (self.iT, self.oT, self.op_names) != (other.iT, other.oT, other.op_names):
            return []
        matches = matcher(other, other.root, self, self.root, opts)
        inputs = [(-1, i) for i in range(len(self.iT))]
        matches_ = []
        for match in matches:
            if set(inputs) == set(match[input] for input in inputs):
                matches_.append({i:match[i] for i in inputs})
        return matches_

    def gt(self, other, opts: SymOpts):
        raise NotImplementedError()


    def __str__(self):
        ret = ",".join([f"{i}:{op}" for i, op in enumerate(self.op_names)]) + "\n  "
        return ret + "\n  ".join(f"{l} -> {r}" for l,r in self.edges)

    def __hash__(self):
        return hash(str(self))

    #TODO verify this works
    def to_comb(self, ns="C", name="C") -> CombProgram:

        #Create symbol mapping
        src_to_sym = {(-1,i): Sym(f"I{i}") for i in range(len(self.iT))}
        for opi in range(self.num_ops):
            src_to_sym.update({(opi, i):Sym(f"t{opi}_{i}") for i in range(len(self.op_oTs[opi]))})

        snk_to_sym = {}
        for src, snk in self.edges:
            assert src in src_to_sym
            snk_to_sym[snk] = src_to_sym[src]
        src_to_sym.update({(self.num_ops, i): Sym(f"O{i}") for i in range(len(self.oT))})

        inDecls = [InDecl(src_to_sym[(-1,i)], nT_to_type(n)) for i, n in enumerate(self.iT)]
        outDecls = [OutDecl(src_to_sym[(self.num_ops, i)], nT_to_type(n)) for i, n in enumerate(self.oT)]

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

    @staticmethod
    def from_comb(comb: CombProgram) -> 'Pattern':
        raise NotImplementedError()
