import functools
import copy
from collections import namedtuple, OrderedDict, Counter
from functools import cached_property
import networkx as nx
from hwtypes import smt_utils as fc

from ..frontend.ast import Comb, Sym, QSym, InDecl, OutDecl
import typing as tp

from .utils import type_to_nT, _list_to_dict, nT_to_type, _list_to_counts, flat, add_to_set, dicts_agree
from ..frontend.ir import CombProgram, AssignStmt, CombSpecialized
from ..frontend.stdlib import CBVSynthConst, GlobalModules, is_dont_care
import itertools as it
from more_itertools import distinct_combinations as multicomb

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
            cur_ais = set()
            if len(comm_info) > 0:
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
    def __init__(self, iT, oT, ops: tp.List[Comb], edges, synth_vals):
        self.iT = iT
        self.oT = oT
        self.ops = ops
        self.num_ops = len(ops)
        self.NI = len(iT)
        self.NO = len(oT)
        self.op_NI = [len(op.get_type()[0]) for op in ops]
        self.op_NO = [len(op.get_type()[1]) for op in ops]
        self.synth_vals = synth_vals
        self.edges = edges
        self.synth_map = {}
        for opi, op in enumerate(ops):
            if isinstance(op, CombSpecialized) and isinstance(op.comb, CBVSynthConst):
                self.synth_map[opi] = synth_vals[len(self.synth_map)]
        assert len(self.synth_map) == len(synth_vals)

        self.children = [[None for _ in range(NI)] for NI in self.op_NI] + [[None for _ in oT]]
        for src, (snki, snka) in self.edges:
            self.children[snki][snka] = src
        assert all(all(ch is not None for ch in op_ch) for op_ch in self.children)
        self.root = (len(ops), 0)

    @classmethod
    def init_prog(cls, iT, oT, ops: tp.List[Comb], P):
        I, O, IK, OK, synth_vals = P
        I, O, IK, OK, synth_vals = (tuple(I), tuple(O), tuple(tuple(IKi) for IKi in IK), tuple(tuple(OKi) for OKi in OK), tuple(synth_vals))
        NI = len(iT)
        NO = len(oT)
        op_NI = [len(op.get_type()[0]) for op in ops]
        op_NO = [len(op.get_type()[1]) for op in ops]
        num_ops = len(ops)

        assert len(IK) == len(ops)
        assert len(OK) == len(ops)
        assert all(len(IKi)==NI for IKi, NI in zip(IK, op_NI))
        assert all(len(OKi)==NO for OKi, NO in zip(OK, op_NO))
        for i, op in enumerate(ops):
            op_iT, op_oT = op.get_type()
            assert len(op_iT) == len(IK[i])
            assert len(op_oT) == len(OK[i])
        src_to_node = {i:(-1,i) for i in range(NI)}
        src_to_node.update({i+NI:(i,0) for i in range(num_ops)})
        edges = []
        for i, IKi in enumerate((*IK, O)):
            for j, l in enumerate(IKi):
                if l < NI:
                    src = (-1, l)
                else:
                    src = None
                    for idx,o in enumerate(OK):
                        if l in o:
                            src = (idx,o.index(l))
                            break
                    assert src is not None
                snk = (i, j)
                edges.append((src, snk))

        return cls(iT, oT, ops, edges, synth_vals)

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

    @cached_property
    def op_cnt_no_dont_cares(self):
        return _list_to_counts(op.qualified_name for op in self.ops if not (isinstance(op, CombSpecialized) and is_dont_care(op.comb)))

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
         for es_so, synth_vals in self.enum_same_op(self.edges):
            for es_c in self.enum_comm(es_so):
                yield es_c,synth_vals


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
            yield (I, tuple(O), tuple(tuple(IKi) for IKi in IK), tuple(tuple(OKi) for OKi in OK), self.synth_vals)


    #For programs
    def enum_input_perm(self, PL):
        I = PL[0]
        NI = len(I)
        NL = len(PL[3])
        for iperm in it.permutations(I):
            map = {i:j for i, j in enumerate(iperm)}
            mapL = {**map, **{i+NI:i+NI for i in range(NL)}}
            yield IPerm(PL, mapL)

    def patL(self, pat_enc, op_mapping):
        allp = []
        for edges,synth_vals in self.enum_CK():
            pat = Pattern(self.iT, self.oT, self.ops, edges, synth_vals)
            allp.append(pat_enc.match_one_pattern(pat, op_mapping))
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
            new_synth_vals = [self.synth_map[op_map[opi]] for opi in sorted(self.synth_map.keys())]
            es = []
            for (src_i, src_a), (snk_i, snk_a) in edges:
                new_src = (op_map[src_i], src_a)
                new_snk = (op_map[snk_i], snk_a)
                es.append((new_src, new_snk))
            yield es, new_synth_vals


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
        if self.synth_vals != other.synth_vals:
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

    def to_comb(self, ns="C", name="C") -> CombProgram:
        prog = list(it.islice(self.enum_prog(self.edges), 1))[0]
        I, O, IK, OK, _ = prog
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

        BV = GlobalModules['bv']
        opi_to_assign = {}
        for opi, op in enumerate(self.ops):
            lhss = [src_to_sym[(opi, i)] for i in range(len(OK[opi]))]
            args = [snk_to_sym[(opi, i)] for i in range(len(IK[opi]))]
            if opi in self.synth_map:
                # convert synth_consts to c_const
                assert len(op.pargs) == 1
                op = BV.c_const[op.pargs[0].value, self.synth_map[opi]]

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


    def topological_sort(self):
        g = nx.DiGraph()
        for (src, _), (snk, _) in self.edges:
            g.add_edge(src, snk)
        for opi in range(self.num_ops+1):
            g.add_edge(-1, opi)
        for opi in range(self.num_ops):
            g.add_edge(opi, self.num_ops)

        order = list(nx.topological_sort(g))
        assert order[0] == -1
        assert order[-1] == self.num_ops
        return order


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
    ops_no_dont_cares = [op for op in ops if not (isinstance(op, CombSpecialized) and is_dont_care(op.comb))]
    op_no_dont_cares_dict = _list_to_dict(op.qualified_name for op in ops_no_dont_cares)

    pat_op_cnts = {}
    for pat in pats:
        for op_name, cnts in pat.op_cnt_no_dont_cares.items():
            pat_op_cnts[op_name] = pat_op_cnts.get(op_name, 0) + cnts

    for chosen_ops in it.product(*[[(op_name, selection) for selection in multicomb(op_no_dont_cares_dict[op_name], cnt)] for op_name,cnt in pat_op_cnts.items()]):
        chosen_ops = {op_name:selection for op_name,selection in chosen_ops} 
        pat_to_enc_map = {}
        curr_ops = []
        #Find one allocation of pat ops to ops
        synth_vals = []
        pmap = {}
        for pi, pat in enumerate(pats):
            synth_vals += pat.synth_vals
            for opi, pat_op in enumerate(pat.ops):
                if pat_op.qualified_name in chosen_ops:
                    original_opi = chosen_ops[pat_op.qualified_name][0]
                    chosen_ops[pat_op.qualified_name] = chosen_ops[pat_op.qualified_name][1:]
                    curr_ops.append(ops[original_opi])
                    pmap[(pi, opi)] = len(curr_ops) - 1
                    pat_to_enc_map[len(curr_ops) - 1] = original_opi
                else:
                    assert is_dont_care(pat_op.comb)
                    curr_ops.append(pat_op)
                    pmap[(pi,opi)] = len(curr_ops)-1
        assert all(len(opis) == 0 for _,opis in chosen_ops.items())

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
                snk = (len(curr_ops), snka)
                _, o_srcs = pat_edges[srci]
                edges.append((o_srcs[srca], snk))
            else:
                _, srcs = pat_edges[srci]
                i_edges, _ = pat_edges[snki]
                for snk in i_edges[snka]:
                    edges.append((srcs[srca], snk))
        yield Pattern(iT, oT, curr_ops, edges, synth_vals),pat_to_enc_map











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


def onepat(P, L, synth_vals, synth_vars):
    #Output
    cond = [fc.And([Pi == Li for Pi, Li in zip(P[1], L[1])])]

    #K ins
    cond.append(fc.And([fc.And([Pij==Lij for Pij, Lij in zip(Pi, Li)]) for Pi, Li in zip(P[2], L[2])]))

    #K outs
    cond.append(fc.And([fc.And([Pij==Lij for Pij, Lij in zip(Pi, Li)]) for Pi, Li in zip(P[3], L[3])]))

    # synthesized values
    cond.append(fc.And([vars == vals for vars,vals in zip(synth_vars, synth_vals)]))
    return fc.And(cond).to_hwtypes()


def IPerm(P, map):
    O = tuple(map[l] for l in P[1])
    IK = tuple(tuple(map[IKij] for IKij in IKi) for IKi in P[2])
    return P[0], O, IK, P[3]

class PatternMatch:
    def __init__(self):
        # a:b where a is a forall src in from_pat (an input or dont care), corresponding to src b in to_pat 
        # a and b are tuples
        self.forall_map = {}

        # a:b where a is an opi in from_pat, corresponding to opi b to to_pat 
        # a and b are ints
        self.opi_map = {}

        # a:b where the sink a in from_pat connects to the src b in to_pat
        # a and b are tuples
        self.edge_map = {}

    def to_tuple(self):
        return (tuple(self.forall_map.items()), tuple(self.opi_map.items()), tuple(self.edge_map.items()))

    def update(self, other):
        assert isinstance(other, type(self))
        self.forall_map.update(other.forall_map)
        self.opi_map.update(other.opi_map)
        self.edge_map.update(other.edge_map)
    
    @classmethod
    def merge(cls, a, b):
        assert isinstance(a, cls)
        assert isinstance(b, cls)
        ret = cls()
        ret.forall_map = {**a.forall_map, **b.forall_map}
        ret.opi_map = {**a.opi_map, **b.opi_map}
        ret.edge_map = {**a.edge_map, **b.edge_map}
        return ret

    @classmethod
    def matches_agree(cls, a, b):
        assert isinstance(a, cls)
        assert isinstance(b, cls)
        return (dicts_agree(a.forall_map, b.forall_map) and 
                dicts_agree(a.opi_map, b.opi_map) and 
                dicts_agree(a.edge_map, b.edge_map))

    def __hash__(self):
        return hash(frozenset(self.forall_map.items()) | 
                    frozenset(self.opi_map.items()) | 
                    frozenset(self.edge_map.items()))

    def __eq__(self, other):
        return (isinstance(other, type(self)) and
            self.forall_map == other.forall_map and
            self.opi_map == other.opi_map and
            self.edge_map == other.edge_map
        )

class PatternMatcher:
    def __init__(self, from_pat: Pattern, to_pat: Pattern, opts):
        self.from_pat = from_pat
        self.to_pat = to_pat
        self.opts = opts
        self.mem = {}
    

    # Finds all matches where from_pat can be a subgraph anywhere in to_pat.
    def match_all(self):
        # Since from_pat is likely a subgraph of to_pat, having same_opts not
        # being True here does not really make sense since from_pat likely has less ops
        assert self.opts.same_op

        from_op_matches = dict()

        from_topo_sort = self.from_pat.topological_sort()[1:-1]
        for from_opi in from_topo_sort:
            for to_opi in range(self.to_pat.num_ops):
                if (from_opi, to_opi) in self.mem:
                    m = self.mem[(from_opi, to_opi)]
                else:
                    m = self.match_from_src((from_opi, 0), (to_opi, 0))
                    self.mem[(from_opi, to_opi)] = m
                from_op_matches.setdefault(from_opi, []).extend(m)
        
        from_output_ops = set()
        for (srci, _),_ in self.from_pat.out_edges:
            from_output_ops.add(srci)
        
        matches = set()
        for partial_matches in it.product(*[from_op_matches[opi] for opi in from_output_ops]):
            # store all solutions where the dicts agree on the same mappings
            merged_match = PatternMatch()
            valid_sol = True
            for m in partial_matches:
                if not PatternMatch.matches_agree(m, merged_match):
                    valid_sol = False 
                    break

                merged_match.update(m)

            if valid_sol:
                assert all((opi in merged_match.opi_map or is_dont_care(self.from_pat.ops[opi].comb)) for opi in range(self.from_pat.num_ops))
                assert all(((opi, arg) in merged_match.edge_map) for opi in range(self.from_pat.num_ops) for arg in range(self.from_pat.op_NI[opi]))
                matches.add(merged_match)
        
        return [m for m in matches]


    def match_from_src(self, from_src, to_src, curr_match = None):
        if curr_match is None:
            curr_match = PatternMatch()

        from_opi, from_arg = from_src
        to_opi, to_arg = to_src

        # inputs and dont cares have the corresponding to_pat src added to the mapping
        if from_opi == -1 or is_dont_care(self.from_pat.ops[from_opi].comb):
            if from_src in curr_match.forall_map:
                if curr_match.forall_map[from_src] == to_src:
                    return [curr_match]
                return []
            else:
                curr_match = copy.deepcopy(curr_match)
                curr_match.forall_map[from_src] = to_src
                return [curr_match]

        if to_opi == -1:
            # input of to_pat but not input of from_pat
            return []

        if from_opi in curr_match.opi_map:
            if curr_match.opi_map[from_opi] != to_opi:
                return []
        if (from_opi, to_opi) in self.mem:
            return [PatternMatch.merge(m,curr_match) for m in self.mem[(from_opi, to_opi)] if PatternMatch.matches_agree(m, curr_match)]
        if self.from_pat.ops[from_opi].qualified_name != self.to_pat.ops[to_opi].qualified_name:
            return []
        if from_opi in self.from_pat.synth_map:
            assert to_opi in self.to_pat.synth_map
            if self.from_pat.synth_map[from_opi] != self.to_pat.synth_map[to_opi]:
                return []
        
        curr_match = copy.deepcopy(curr_match)
        curr_match.opi_map[from_opi] = to_opi
        
        comm_orderings = [self.to_pat.children[to_opi]]
        if self.opts.comm:
            to_srcs = self.to_pat.children[to_opi] 
            comm_info = self.to_pat.ops[to_opi].comm_info
            assert all(isinstance(l, list) for l in comm_info)
            assert self.from_pat.ops[from_opi].comm_info == comm_info
            assert set(flat(comm_info)) == set(range(len(to_srcs)))
            comm_orderings = []
            for poss in it.product(*[it.permutations(comm) for comm in comm_info]):
                comm = [None for _ in to_srcs]
                for f,t in zip(flat(comm_info), flat(poss)):
                    comm[t] = to_srcs[f]
                assert all(v is not None for v in comm)
                comm_orderings.append(comm)

        all_matches = []
        for to_ordering in comm_orderings:
            curr_matches = [curr_match]
            for from_arg,(from_src, to_src) in enumerate(zip(self.from_pat.children[from_opi], to_ordering)):
                temp = []
                for m in curr_matches:
                    m = copy.deepcopy(m)
                    m.edge_map[(from_opi, from_arg)] = to_src
                    temp.extend(self.match_from_src(from_src, to_src, m))
                curr_matches = temp

            #here we ensure the connections made to inputs are valid based on comm rules
            for m in curr_matches:
                #the expected connetions based on the connections in from_pat, translated into
                #to_pat using the opi mappings and special cases for inputs and dont_cares
                expected_conn = []
                for (opi,arg) in self.from_pat.children[from_opi]:
                    if opi == -1 or is_dont_care(self.from_pat.ops[opi].comb):
                        expected_conn.append(m.forall_map[(opi,arg)])
                    else:
                        expected_conn.append((m.opi_map[opi], arg))
                
                #the actual connections made based on the match snk:src entries
                actual_conn = [m.edge_map[(from_opi, i)] for i in range(self.from_pat.ops[from_opi].num_inputs)]

                if self.opts.comm:
                    # since comm is True, we ensure the comm groups match for expected and actual connections
                    comm_info = self.to_pat.ops[to_opi].comm_info
                    if all((Counter(actual_conn[c] for c in comm) == Counter(expected_conn[c] for c in comm)) 
                            for comm in comm_info):
                        all_matches.append(m)
                else:
                    # since no comm considered, compare expected and actual connections directly
                    if expected_conn == actual_conn:
                        all_matches.append(m)
        return all_matches
