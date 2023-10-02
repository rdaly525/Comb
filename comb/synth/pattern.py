import functools
from collections import namedtuple
from functools import cached_property
import networkx as nx
from hwtypes import smt_utils as fc

from ..frontend.ast import Comb, Sym, QSym, InDecl, OutDecl
import typing as tp

from .utils import type_to_nT, _list_to_dict, nT_to_type, _list_to_counts, flat, add_to_set
from ..frontend.ir import CombProgram, AssignStmt
import itertools as it

#Represnts the raw dag structure of a particular pattern
#Inputs are encoded as -1
#Outputs are encoded as num_ops

SymOpts = namedtuple('SymOpts', ('comm', 'same_op', 'input_perm'), defaults=(False,)*3)

#dedupliates list of dicts
def dedup(f):
    @functools.wraps(f)
    def dec(*args, **kwargs):
        ret = f(*args, **kwargs)
        return list({str(v):v for v in ret}.values())
    return dec

#(canonicalize comm=True means allow ckecing comm
#(canonicalize same ops means
@dedup
def matcher(from_pat, from_root, to_pat, to_root, opts: SymOpts):
    r = from_pat
    r_root = from_root
    l = to_pat
    l_root = to_root
    def match(l_src, r_src, ctx) -> tp.List[dict]:
        l_opi, l_arg = l_src
        r_opi, r_arg = r_src
        #Check if already done or if mismatch

        if r_opi == -1:
            if r_src in ctx:
                if ctx[r_src]==l_src:
                    return [ctx]
                else:
                    #Fanout does not match
                    return []
            else:
                ctx = {r_src: l_src, **ctx}
            return [ctx]

        if l_arg != r_arg:
            return []

        if r_opi in ctx:
            if ctx[r_opi]==l_opi:
                return [ctx]
            else:
                #Fanout does not match
                return []

        if opts.same_op:
            if l.op_names_with_io[l_opi] != r.op_names_with_io[r_opi]:
                return []
        else:
            if l_opi != r_opi:
                return []
        l_poss_args = [l.children[l_opi]]
        #Find all possible commititive permutations
        if opts.comm and l_opi in range(l.num_ops):
            l_args = l.children[l_opi] #[0,1,2,3]
            comm_info = l.ops[l_opi].comm_info
            assert all(isinstance(l, list) for l in comm_info)
            assert r.ops[r_opi].comm_info == comm_info
            #Append comm_info with extra args
            cur_ais = functools.reduce(lambda s0,s1: s0|s1, [set(c) for c in comm_info])
            assert isinstance(cur_ais, set)
            assert cur_ais == set(range(len(l_args)))
            l_poss_args = []
            for poss in it.product(*[it.permutations(comm) for comm in comm_info]):
                comm_l_args = [None for _ in l_args]
                for f,t in zip(flat(comm_info), flat(poss)):
                    comm_l_args[t] = l_args[f]
                assert all(v is not None for v in comm_l_args)
                l_poss_args.append(comm_l_args)

        matched = []
        #For each comm ordering
        for l_args in l_poss_args:
            ctxs = [ctx]
            #For each op argument
            for l_src, r_src in zip(l_args, r.children[r_opi]):
                ctxs_ = []
                for ctx_ in ctxs:
                    m_ctxs = match(l_src, r_src, ctx_)
                    ctxs_.extend(m_ctxs)
                ctxs = ctxs_
            matched.extend(ctxs)
        assert all(r_opi not in ctx for ctx in matched)
        matched = [{**ctx, r_opi:l_opi} for ctx in matched]
        return matched
    return match(l_root, r_root, {})


def filter_eq(f):
    eq_set = set()
    @functools.wraps(f)
    def wrapped(*args, **kwargs):
        for v in f(*args, **kwargs):
            if v in eq_set:
                continue
            yield v
    return wrapped

#class Program:
#    def __init__(self, ops: tp.List[Comb], P):
#        self.ops = ops
#        I, O, IK, OK = P
#        assert len(IK) == len(ops)
#        assert len(OK) == len(ops)
#        for i, op in enumerate(ops):
#            iT, oT = op.get_type()
#            assert len(oT) == 1
#            assert len(iT) == len(IK[i])
#            iT = [type_to_nT(t) for t in iT]
#            assert all(t==iT[0] for t in iT)
#        self.NI =
#        self.p = (tuple(I), O, tuple(tuple(IKi) for IKi in IK), tuple(OK))
#
#    def __eq__(self, other:Pattern):
#        if not isinstance(other, Pattern)
#        pat =

class Pattern:
    def __init__(self, iT, oT, ops: tp.List[Comb], P, is_pat):
        self.iT = iT
        self.oT = oT
        self.ops = ops
        self.num_ops = len(ops)
        self.NI = len(iT)
        self.NO = len(oT)
        self.op_NI = [len(op.get_type()[0]) for op in ops]
        self.op_NO = [len(op.get_type()[1]) for op in ops]
        if is_pat:
            self.edges = P
        else:
            self.init_prog(P)

        self.children = [[None for _ in range(NI)] for NI in self.op_NI] + [[None for _ in oT]]
        for src, (snki, snka) in self.edges:
            self.children[snki][snka] = src
        assert all(all(ch is not None for ch in op_ch) for op_ch in self.children)
        self.root = (len(ops), 0)

    def init_prog(self, P):
        I, O, IK, OK = P
        I, O, IK, OK = (tuple(I), tuple(O), tuple(tuple(IKi) for IKi in IK), tuple(tuple(OKi) for OKi in OK))
        ops = self.ops
        assert len(IK) == len(ops)
        assert len(OK) == len(ops)
        assert all(len(IKi)==NI for IKi, NI in zip(IK, self.op_NI))
        assert all(len(OKi)==NO for OKi, NO in zip(OK, self.op_NO))
        for i, op in enumerate(ops):
            iT, oT = op.get_type()
            assert len(iT) == len(IK[i])
            assert len(oT) == len(OK[i])
        src_to_node = {i:(-1,i) for i in range(self.NI)}
        src_to_node.update({i+self.NI:(i,0) for i in range(self.num_ops)})
        self.edges = []
        for i, IKi in enumerate((*IK, O)):
            for j, l in enumerate(IKi):
                if l < self.NI:
                    src = (-1, l)
                else:
                    src = None
                    for idx,o in enumerate(OK):
                        if l in o:
                            src = (idx,o.index(l))
                            break
                    assert src is not None
                snk = (i, j)
                self.edges.append((src, snk))

    @cached_property
    def op_names(self):
        return [op.qualified_name for op in self.ops]

    @cached_property
    def name(self):
        return "[" + ",".join(s for s in self.op_names) + "]"

    @cached_property
    def op_names_with_io(self):
        return [op.qualified_name for op in self.ops] + ["IO"]

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

    #def enum_all_equal(self, en_I):
    #    eq_set = set()
    #    for es_ip in self.enum_input_perm(self.edges, en_I):
    #        for es_so in self.enum_same_op(es_ip):
    #            for es_c in self.enum_comm(es_so):
    #                for prog in self.enum_prog(es_c):
    #                    #yield prog
    #                    if add_to_set(eq_set, prog):
    #                        yield prog

    def enum_CK(self):
         for es_so in self.enum_same_op(self.edges):
            for es_c in self.enum_comm(es_so):
                yield es_c



    def enum_prog(self, edges):
        I = tuple(i for i in range(self.NI))
        IK = [[None for _ in range(NI)] for NI in self.op_NI]
        OK = [[None for _ in range(NO)] for NO in self.op_NO]
        O = [None for _ in range(self.NO)]
        g = nx.DiGraph()
        for (src, _), (snk, _) in edges:
            g.add_edge(src, snk)
        #Force inouts to be first
        for opi in range(self.num_ops+1):
            g.add_edge(-1, opi)
        for opi in range(self.num_ops):
            g.add_edge(opi, self.num_ops)

        for order in nx.all_topological_sorts(g):
            #OK = [o+self.NI for o in order]
            l = self.NI
            for opi in order[1:-1]:
                for o_num in range(len(OK[opi])):
                    OK[opi][o_num] = l
                    l += 1
            #Set all of IK and O
            for (srci, srca), (snki, snka) in edges:
                if srci==-1:
                    src_l = srca
                else:
                    src_l = OK[srci][srca]
                if snki==self.num_ops:
                    O[snka] =  src_l
                else:
                    IK[snki][snka] = src_l
            assert all(l is not None for l in O)
            assert all(all(l is not None for l in IKi) for IKi in IK)
            assert all(all(l is not None for l in OKi) for OKi in OK)
            yield (I, tuple(O), tuple(tuple(IKi) for IKi in IK), tuple(tuple(OKi) for OKi in OK))


    #For programs
    def enum_input_perm(self, PL):
        I = PL[0]
        NI = len(I)
        NL = len(PL[3])
        for iperm in it.permutations(I):
            map = {i:j for i, j in enumerate(iperm)}
            mapL = {**map, **{i+NI:i+NI for i in range(NL)}}
            yield IPerm(PL, mapL)


    def patL(self, L):
        allp = []
        for PL in all_prog(self.enum_CK(), self.enum_prog):
            for PL_ in self.enum_input_perm(PL):
                allp.append(onepat(PL_, L))
        return fc.Or(allp).to_hwtypes()



    def enum_comm(self, edges):
        for op_poss in it.product(*[it.product(*[it.permutations(comm) for comm in op.comm_info]) for op in self.ops]):
            map = {self.num_ops:{i:i for i in range(len(self.oT))}} #[opi][ai]
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


    def equal(self, other: 'Pattern'):
        opts = SymOpts(comm=True, same_op=True)
        matches = self.equal_with_match(other, opts)
        return len(matches)>0
    #def equal(self, other, opts: SymOpts):
    #    matches = self.equal_with_match(other, opts)
    #    if opts.input_perm:
    #        raise NotImplementedError()
    #        inputs = [(-1, i) for i in range(len(self.iT))]
    #        matched_inputs = (matches[input] for input in inputs)
    #        return set(inputs) == set(matched_inputs)
    #    else:
    #        return any(all((-1, i)==match[(-1,i)] for i in range(len(self.iT))) for match in matches)

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
        prog = list(it.islice(self.enum_prog(self.edges), 1))[0]
        I, O, IK, OK = prog
        #Create symbol mapping
        src_to_sym = {(-1,i): Sym(f"I{i}") for i in range(len(I))}
        for opi,num_o in enumerate(self.op_NO):
            for n in range(num_o):
                src_to_sym.update({(opi, n):Sym(f"t{opi}_{n}")})

        snk_to_sym = {}
        for src, snk in self.edges:
            if src not in src_to_sym:
                print(src, snk)
                raise ValueError
            assert src in src_to_sym
            snk_to_sym[snk] = src_to_sym[src]
        src_to_sym.update({(self.num_ops, i): Sym(f"O{i}") for i in range(len(self.oT))})

        inDecls = [InDecl(src_to_sym[(-1,i)], nT_to_type(n)) for i, n in enumerate(self.iT)]
        outDecls = [OutDecl(src_to_sym[(self.num_ops, i)], nT_to_type(n)) for i, n in enumerate(self.oT)]

        opi_to_assign = {}
        for opi, op in enumerate(self.ops):
            lhss = [src_to_sym[(opi, i)] for i in range(len(OK[opi]))]
            args = [snk_to_sym[(opi, i)] for i in range(len(IK[opi]))]
            opi_to_assign[opi] = AssignStmt(lhss, [op.call_expr([], args)])
        #Create output decl O0, O1 = t0_1, t2_2
        out_lhs = [src_to_sym[(self.num_ops, i)] for i in range(len(self.oT))]
        out_rhs = [snk_to_sym[(self.num_ops, i)] for i in range(len(self.oT))]
        out_assign = AssignStmt(out_lhs, out_rhs)

        g = nx.DiGraph()
        for (src, _), (snk, _) in self.edges:
            g.add_edge(src, snk)
        try:
            order = list(nx.topological_sort(g))
        except nx.NetworkXException:
            print(g)
            raise ValueError

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


def enum_dags(iT, oT, pats: tp.List[Pattern]):
    NIs = [len(p.iT) for p in pats]
    NOs = [len(p.oT) for p in pats]
    Npat = len(NIs)

    #Create a set of all sources/snks sorted by type
    srcs = [(-1, i) for i in range(len(iT))]
    for i, NOi in enumerate(NOs):
        srcs.extend((i, j) for j in range(NOi))
    snks = [(Npat, i) for i in range(len(oT))]
    for i, NIi in enumerate(NIs):
        snks.extend((i, j) for j in range(NIi))

    #This strategy will produce invalid graphs
    #Easy filter to remove most of the bad connections
    def invalid_edge(src, snk):
        if src[0] == -1:
            srcT = iT[src[1]]
        else:
            srcT = pats[src[0]].oT[src[1]]
        if snk[0] == Npat:
            snkT = oT[snk[1]]
        else:
            snkT = pats[snk[0]].iT[snk[1]]

        return ((src[0] == snk[0])) or ((src[0], snk[0]) == (-1, Npat) or (srcT != snkT))
    def valid_dag(edges):
        used_pats = set(srci for (srci, _),_ in edges if srci >= 0)
        used_Is = set(pos for (srci, pos),_ in edges if srci == -1)
        if not len(used_pats) == Npat:
            return False
        if not len(used_Is) == len(iT):
            return False
        if not set(snk for _,snk in edges) == set(snks):
            return False

        bad_edge = any(invalid_edge(src, snk) for src, snk in edges)
        return not bad_edge

    src_poss = [srcs for _ in snks]
    graphs = []
    for src_list in it.product(*src_poss):
        edges = list(zip(src_list, snks))
        if valid_dag(edges):
            if is_dag(edges):
                graphs.append(edges)
    return graphs

def is_dag(edges):
    g = nx.DiGraph()
    for (src, _), (snk, _) in edges:
        g.add_edge(src, snk)
    return nx.is_directed_acyclic_graph(g)


def composite_pat(iT, oT, dag, pats:tp.List[Pattern], ops) -> Pattern:
    op_names = [op.qualified_name for op in ops]
    #Find one allocation of pat ops to ops
    op_map = [None for _ in op_names]
    pmap = {}
    for pi, pat in enumerate(pats):
        for opi, pat_op in enumerate(pat.op_names):
            for i, op in enumerate(op_names):
                if (op_map[i] is None) and op==pat_op:
                    op_map[i] = (pi, opi)
                    pmap[(pi, opi)] = i
                    break
    assert all(m is not None for m in op_map)
    pat_edges = {}
    edges = []
    for pi, pat in enumerate(pats):
        i_edges = {}
        o_srcs = [None for _ in range(pat.NO)]
        m_edges = []
        for (srci, srca), (snki, snka) in pat.edges:
            if snki == pat.num_ops:
                assert (pi, srci) in pmap
                new_srci = pmap[(pi, srci)]
                o_srcs[snka] = (new_srci, srca)
            elif srci == -1:
                assert (pi, snki) in pmap
                new_snki = pmap[(pi, snki)]
                i_edges.setdefault(srca,[]).append((new_snki, snka))
            else:
                assert (pi, srci) in pmap
                assert (pi, snki) in pmap
                new_srci = pmap[(pi, srci)]
                new_snki = pmap[(pi, snki)]
                m_edges.append(((new_srci, srca), (new_snki, snka)))
        assert all([src is not None for src in o_srcs])
        edges.extend(m_edges)
        pat_edges[pi] = (i_edges, o_srcs)
    for (srci, srca), (snki, snka) in dag:
        if srci==-1:
            src = (srci, srca)
            i_edges, _ = pat_edges[snki]
            for snk in i_edges[snka]:
                edges.append((src, snk))
        elif snki == len(pats):
            snk = (len(op_names), snka)
            _, o_srcs = pat_edges[srci]
            edges.append((o_srcs[srca], snk))
        else:
            _, srcs = pat_edges[srci]
            i_edges, _ = pat_edges[snki]
            for snk in i_edges[snka]:
                edges.append((srcs[srca], snk))
    return Pattern(iT, oT, ops, edges, is_pat=True)











#def enum_dags(goal_iT, goal_oT, pats: tp.List[Pattern]):
#    pat_iTs = [_list_to_dict(p.iT) for p in pats]
#    pat_oTs = [_list_to_dict(p.oT) for p in pats]
#
#    #Create a set of all sources/snks sorted by type
#    srcs = {n:[(-1, i) for i in ids] for n, ids in _list_to_dict(goal_iT).items()}
#    for pi, pat_oT in enumerate(pat_oTs):
#        for n, ids in pat_oT.items():
#            srcs.setdefault(n, []).extend((pi, i) for i in ids)
#    snks = {n:[(len(pats), i) for i in ids] for n, ids in _list_to_dict(goal_oT).items()}
#    for pi, pat_iT in enumerate(pat_iTs):
#        for n, ids in pat_iT.items():
#            snks.setdefault(n, []).extend((pi, i) for i in ids)
#
#
#    #This strategy will produce invalid graphs
#    #Easy filter to remove most of the bad connections
#    def invalid_edge(src, snk):
#        return ((src[0] == snk[0])) or ((src[0], snk[0]) == (-1, len(pats)))
#    all_src = flat([srcs_ for srcs_ in srcs.values()])
#    def invalid_dag(edges):
#        used_srcs = set(src for src,_ in edges)
#        all_used = all(src in used_srcs for src in all_src)
#        bad_edge = any(invalid_edge(src, snk) for src, snk in edges)
#        return (not all_used) or bad_edge
#        #each source should be in edge list
#
#    src_poss = []
#    snk_list = []
#    for n, n_snks in snks.items():
#        snk_list += n_snks
#        src_poss += [srcs[n] for _ in n_snks]
#
#    graphs = []
#    for src_list in it.product(*src_poss):
#        edges = list(zip(src_list, snk_list))
#        if not invalid_dag(edges):
#            graphs.append(edges)
#    return graphs
def all_prog(pat_enum, prog_enum):
    #Only enumerate unique programs
    eq = set()
    for pat in pat_enum:
        for prog in prog_enum(pat):
            if add_to_set(eq, prog):
                yield prog


def onepat(P, L):
    #Output
    cond = [fc.And([Pi == Li for Pi, Li in zip(P[1], L[1])])]

    #K ins
    cond.append(fc.And([fc.And([Pij==Lij for Pij, Lij in zip(Pi, Li)]) for Pi, Li in zip(P[2], L[2])]))

    #K outs
    cond.append(fc.And([fc.And([Pij==Lij for Pij, Lij in zip(Pi, Li)]) for Pi, Li in zip(P[3], L[3])]))
    return fc.And(cond).to_hwtypes()


def IPerm(P, map):
    O = tuple(map[l] for l in P[1])
    IK = tuple(tuple(map[IKij] for IKij in IKi) for IKi in P[2])
    return P[0], O, IK, P[3]
