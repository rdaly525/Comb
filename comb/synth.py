import collections
import itertools as it

from pysmt.fnode import FNode

import hwtypes.smt_utils as fc
import hwtypes as ht
from dataclasses import dataclass
from .ast import Comb, BVValue, OutDecl, TypeCall, BVType, InDecl, Sym, Type
from .ir import AssignStmt, QSym, _make_list, CombProgram, CallExpr, Obj
import typing as tp
import pysmt.shortcuts as smt
from pysmt.logics import QF_BV, Logic
from .stdlib import GlobalModules, make_bv_const
import networkx as nx

#import more_itertools as mit

class IterLimitError(Exception):
    pass

#Represnts the raw dag structure of a particular pattern
class Pattern:
    def __init__(self, ops):
        self.ops = ops
        self.nodes = ['In'] + list(range(len(ops))) + ['Out']
        self.edges = []
    def add_edge(self, lhs, rhs):
        assert len(lhs)==2 and len(rhs)==2
        assert lhs[0] in self.nodes
        assert rhs[0] in self.nodes
        self.edges.append((lhs, rhs))

@dataclass
class SolverOpts:
    logic: Logic = QF_BV
    max_iters: int = 1000
    solver_name: str = "z3"
    verbose: int = 0

def smt_solve_all(f, opts: SolverOpts = SolverOpts()):
    E_vars = f.get_free_variables()
    with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
        solver.add_assertion(f)
        while solver.solve():
            sol = {v: solver.get_value(v) for v in E_vars}
            yield sol
            #Construct sol
            sol_term = smt.Bool(True)
            for var, val in sol.items():
                sol_term = smt.And(sol_term, smt.Equals(var, val))
            solver.add_assertion(smt.Not(sol_term))

def _int_to_pysmt(x: int, sort):
    if sort.is_bv_type():
        return smt.BV(x % sort.width, sort.width)
    else:
        assert sort.is_bool_type()
        return smt.Bool(bool(x))

def _to_int(x):
    assert x.is_constant()
    return int(x.constant_value())

SBV = ht.SMTBitVector
SBit = ht.SMTBit

def flat(l):
    return [l__ for l_ in l for l__ in l_]


def print_e(e):
    print()
    for k, v in e.items():
        print(f"  {k}: {v}")

@dataclass
class Cegis:
    query: ht.SMTBit
    E_vars: tp.Iterable['freevars']

    def cegis(self, opts: SolverOpts=SolverOpts(), exclude_list=[]):
        if opts.verbose==2:
            show_e = True
            show_iter = True
        elif opts.verbose:
            show_e = False
            show_iter = True
        else:
            show_e = False
            show_iter = False
        assert opts.max_iters > 0
        query = self.query.value

        for sol in exclude_list:
            sol_term = smt.Bool(True)
            for var, val in sol.items():
                sol_term = smt.And(sol_term, smt.Equals(var, val))
            query = smt.And(query, smt.Not(sol_term))

        #get exist vars:
        E_vars = set(var.value for var in self.E_vars)  # forall_vars
        A_vars = query.get_free_variables() - E_vars  # exist vars

        with smt.Solver(logic=opts.logic, name=opts.solver_name) as solver:
            solver.add_assertion(smt.Bool(True))

            # Start with checking all A vals beings 0
            A_vals = {v: _int_to_pysmt(0, v.get_type()) for v in A_vars}
            solver.add_assertion(query.substitute(A_vals).simplify())
            for i in range(opts.max_iters):
                if show_iter and i%10==0:
                    print(f".{i}", end='', flush=True)
                E_res = solver.solve()

                if not E_res:
                    if show_iter:
                        print("UNSAT")
                    return None
                else:
                    E_guess = {v: solver.get_value(v) for v in E_vars}
                    if show_e and i%100==50:
                        print_e(E_guess)
                    query_guess = query.substitute(E_guess).simplify()
                    model = smt.get_model(smt.Not(query_guess), solver_name=opts.solver_name, logic=opts.logic)
                    if model is None:
                        if show_iter:
                            print("SAT")
                        return E_guess
                    else:
                        A_vals = {v: model.get_value(v) for v in A_vars}
                        solver.add_assertion(query.substitute(A_vals).simplify())

            raise IterLimitError(f"Unknown result in CEGIS in {opts.max_iters} number of iterations")

    #enum_fun takes a single solution and enumerates all 'permutations' of that solution to add to the exclude list
    def cegis_all(self, opts: SolverOpts=SolverOpts(), enum_fun=None):
        exclude_list = []
        while True:
            try:
                sol = self.cegis(opts, exclude_list=exclude_list)
            except IterLimitError:
                print("MAXITER")
                break
            if sol is None:
                break
            if enum_fun is not None:
                new_exclude = list(enum_fun(sol))
                exclude_list += new_exclude
            else:
                exclude_list.append(sol)
            yield sol

@dataclass
class CombSynth:
    comb_type: tp.Tuple[tp.Iterable[Type], tp.Iterable[Type]]
    op_list: tp.List[Comb]
    const_list: tp.Tuple[int] = ()
    loc_type_int: bool = False
    prefix: str = ""

    def __post_init__(self):

        #Spec, and ops cannot have params
        if any(comb.has_params for comb in self.op_list):
            raise ValueError("Cannot synth with non-concrete parameters")
        iTs, oTs = self.comb_type

        # Structure
        input_vars = [T.free_var(f"{self.prefix}__VI_{i}") for i, T in enumerate(iTs)]
        self.input_vars = input_vars

        Ninputs = len(input_vars)
        hard_consts = self.const_list
        Nconsts = len(hard_consts)
        #const_vars = []
        output_vars = [T.free_var(f"{self.prefix}__VO_{i}") for i, T in enumerate(oTs)]
        self.output_vars = output_vars
        op_out_vars = []
        op_in_vars = []
        tot_locs = Ninputs + Nconsts
        for i, op in enumerate(self.op_list):
            assert isinstance(op, Comb)
            op_in_vars.append(op.create_symbolic_inputs(prefix=f"{self.prefix}__V_op{i}"))
            op_out_vars.append(op.create_symbolic_outputs(prefix=f"{self.prefix}__V_op{i}"))
            tot_locs += op.num_outputs
        self.vars = (input_vars, hard_consts, output_vars, op_out_vars, op_in_vars)
        self.tot_locs = tot_locs
        lvar_t = ht.SMTInt if self.loc_type_int and hasattr(ht, "SMTInt") else SBV[tot_locs]

        #These can be hardcoded
        input_lvars = list(range(len(input_vars)))
        Ninputs = len(input_vars)
        hard_const_lvars = list(range(Ninputs, Ninputs +len(hard_consts)))
        op_out_lvars = []
        op_in_lvars = []
        for i, op in enumerate(self.op_list):
            op_out_lvars.append([lvar_t(prefix=f"{self.prefix}__Lt[{i},{j}]") for j in range(op.num_outputs)])
            op_in_lvars.append([lvar_t(prefix=f"{self.prefix}__Li[{i},{j}]") for j in range(op.num_inputs)])
        output_lvars = [lvar_t(prefix=f"{self.prefix}__Lo{i}") for i in range(len(output_vars))]
        self.op_in_lvars = op_in_lvars

        #get list of lvars (existentially quantified in final query)
        self.E_vars = output_lvars + flat(op_out_lvars) + flat(op_in_lvars)
        self.lvars = (input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars)

        self.rhs_lvars = flat(op_in_lvars) + output_lvars

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


    def fix_comm(self, sol):
        comm_ids = [i for i, op in enumerate(self.op_list) if op.commutative]
        v_sols = []
        for i in comm_ids:
            lvars = self.op_in_lvars[i]
            lvals = [sol[lvar.value] for lvar in lvars]
            vals = sorted([(int(sol[lvar.value].constant_value()), li) for li, lvar in enumerate(lvars)])
            v_sols.append({lvars[si].value: lvals[oi] for si, (v, oi) in enumerate(vals)})

        new_sol = dict(sol)
        for d in v_sols:
            new_sol = {**new_sol, **d}
        return new_sol


    def gen_all_program_orders(self, sol):
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        #Create Graph from sol
        lvar_to_nid = {}
        int_to_lval = {}
        for v in input_lvars:
            lvar_to_nid[v] = 'In'
        assert len(hard_const_lvars) == 0
        ln_to_nid = {}

        nids = []
        for li, lvars in enumerate(op_out_lvars):
            tmp_vals = tuple(_to_int(sol[lvar.value]) for lvar in lvars)
            nid = tmp_vals
            nids.append((tmp_vals[0], nid))
            ln_to_nid[li] = nid
            for v, lvar in zip(tmp_vals, lvars):
                lvar_to_nid[v] = nid
                int_to_lval[v] = sol[lvar.value]
        nids = ["In"] + [v for _, v in sorted(nids)] + ["Out"]
        g = nx.DiGraph()
        #Add the edges
        for ti, lvars in enumerate(op_in_lvars):
            op_nid = ln_to_nid[ti]
            tmp_vals = [_to_int(sol[lvar.value]) for lvar in lvars]
            #Add edge to input
            g.add_edge('In', op_nid)
            for v, lvar in zip(tmp_vals, lvars):
                assert v in lvar_to_nid
                g.add_edge(lvar_to_nid[v], op_nid)
                int_to_lval[v] = sol[lvar.value]

        #Add Output edges
        for oval in [_to_int(sol[lvar.value]) for lvar in output_lvars]:
            assert oval in lvar_to_nid
            g.add_edge(lvar_to_nid[oval], "Out")

        for k, lval in int_to_lval.items():
            assert _to_int(lval) == k

        all_lvars = flat(op_in_lvars) + flat(op_out_lvars) + output_lvars
        i_to_lvars = {}
        for lvar in all_lvars:
            v = int(sol[lvar.value].constant_value())
            i_to_lvars.setdefault(v, []).append(lvar)

        def sort_to_sol(sort):
            v_sols = []
            for from_nid, to_nid in zip(nids[1:-1], sort[1:-1]):
                for from_val, to_val in zip(from_nid, to_nid):
                    to_lval = int_to_lval[to_val]
                    v_sols.append({lvar.value: to_lval for lvar in i_to_lvars[from_val]})

            new_sol = dict(sol)
            for d in v_sols:
                new_sol = {**new_sol, **d}
            return new_sol

        #Run the gen all topographical orderings algorithm
        for sort in nx.all_topological_sorts(g):
            new_sol = sort_to_sol(sort)
            yield new_sol


    def gen_op_permutations(self, sol):
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars

        #Get indices of each commutative op
        commute_idxs = []
        for i, op in enumerate(self.op_list):
            if op.commutative:
                commute_idxs.append(i)

        lvar_perms = []
        lvar_list = []
        for i in commute_idxs:
            lvar_list += [lvar.value for lvar in op_in_lvars[i]]
            lvals = [sol[lvar.value] for lvar in op_in_lvars[i]]
            lvar_perms.append(set(it.permutations(lvals)))

        for lvals in it.product(*lvar_perms):
            lval_list = flat([lval_tuple for lval_tuple in lvals])
            new_vals = {lvar: lval for lvar, lval in zip(lvar_list, lval_list)}
            new_sol = {**sol, **new_vals}
            yield new_sol
            #sols.append(new_sol)
        #assert sum([int(sol==_sol) for _sol in sols]) == 1, str([int(sol==_sol) for _sol in sols])
        #return sols

    #Makes sure the typing makes sense for the query
    def types_viable(self):
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

    def pattern_from_solved(self, sol):
        spec_iTs, spec_oTs = self.comb_type
        num_inputs = len(spec_iTs)
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        if len(hard_const_lvars) > 0:
            raise NotImplementedError()
        op_out_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_out_lvars]
        op_in_lvals = [[_to_int(sol[lvar.value]) for lvar in lvars] for lvars in op_in_lvars]
        output_lvals = [_to_int(sol[lvar.value]) for lvar in output_lvars]
        nodes = [(op_out_lvals[i][0], i) for i, _ in enumerate(self.op_list)]
        sorted_nis = [v[1] for v in sorted(nodes)]
        sorted_ops = [self.op_list[ni] for ni in sorted_nis]
        p = Pattern(sorted_ops)
        for opi, lvals in enumerate(op_in_lvals):
            for argi, arg in enumerate(lvals):
                rhs = ()
                p.add_edge(lhs, rhs)




    def comb_from_solved(self, lvals, name: QSym):
        spec_iTs, spec_oTs = self.comb_type

        input_vars, hard_consts, output_vars, op_out_vars, op_in_vars = self.vars
        input_lvars, hard_const_lvars, output_lvars, op_out_lvars, op_in_lvars = self.lvars
        num_inputs = len(spec_iTs)
        #Fill in all the lvars
        output_lvars = [_to_int(lvals[lvar.value]) for lvar in output_lvars]
        def name_from_loc(loc, src=None):
            if loc < num_inputs:
                return Sym(f"I{loc}")
            elif loc < num_inputs + len(hard_consts):
                assert src is not None
                i, j = src
                iT = self.op_list[i].get_type()[0][j].type
                if isinstance(iT, TypeCall):
                    assert isinstance(iT.type, BVType)
                    N = iT.pargs[0].value
                    const_val = hard_consts[loc - num_inputs]
                    return make_bv_const(N, const_val)
                else:
                    raise NotImplementedError()
            else:
                loc = loc - (num_inputs + len(hard_consts))
                return Sym(f"t{loc}")

        out_lvar_vals = {}
        in_lvar_vals = {}
        for i in range(len(op_out_lvars)):
            out_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_out_lvars[i]]
            in_lvar_vals[i] = [_to_int(lvals[lvar.value]) for lvar in op_in_lvars[i]]

        inputs = [InDecl(name_from_loc(i), T) for i, T in enumerate(spec_iTs)]
        outputs = [OutDecl(name_from_loc(output_lvars[i]), T) for i, T in enumerate(spec_oTs)]
        stmts = []
        for i, out_lvars in sorted(out_lvar_vals.items(), key=lambda item: item[1][0]):
            lhss = [name_from_loc(loc) for loc in out_lvars]
            op = self.op_list[i]
            args = [name_from_loc(loc, src=(i,j)) for j, loc in enumerate(in_lvar_vals[i])]
            stmts.append(AssignStmt(lhss, [op.call_expr([], args)]))
        comb = CombProgram(name, [*inputs, *outputs, *stmts])
        return comb


class BuckSynth(Cegis):
    def __init__(
        self,
        spec: Comb,
        op_list: tp.List[Comb],
        const_list: tp.Tuple[int] = (),
        loc_type_int: bool = False,
    ):
        self.cs = CombSynth(spec.get_type(), op_list, const_list, loc_type_int)
        input_vars, hard_consts, output_vars, op_out_vars, op_in_vars = self.cs.vars
        self.spec = spec
        #Formal Spec (P_spec)
        P_spec = []
        for (i, ov) in enumerate(_make_list(self.spec.evaluate(*input_vars))):
            P_spec.append(output_vars[i] == ov)

        And = fc.And
        #Final query:
        #  Exists(L) Forall(V) P_wfp(L) & (P_lib & P_conn) => P_spec
        query = And([
            self.cs.P_wfp,
            fc.Implies(
                And([self.cs.P_lib, self.cs.P_conn]),
                And(P_spec)
            )
        ])
        E_vars = self.cs.E_vars
        super().__init__(query.to_hwtypes(), E_vars)

    # Tactic. Generate all the non-permuted solutions.
    # For each of those solutions, generate all the permutations
    def gen_all_sols(self, permutations=False, opts: SolverOpts=SolverOpts()) -> tp.List[Comb]:
        sols = self.cegis_all(opts)
        if permutations:
            sols = flat([self.cs.gen_op_permutations(sol) for sol in sols])

        combs = [self.cs.comb_from_solved(sol, name=QSym('Solved', f"v{i}")) for i, sol in enumerate(sols)]
        if len(set(c.serialize_body() for c in combs)) != len(combs):
            c0 = combs[0].serialize_body()
            for i in range(1, len(combs)):
                if c0 == combs[i].serialize_body():
                    print(f"BAD!, 0 = {i}")
                    print(combs[0])
                    print(combs[i])
                    print(f"0:", sols[0])
                    print(f"{i}:", sols[i])
            raise ValueError("Somehting went wrong")
        return combs


def verify(comb0: Comb, comb1: Comb, logic=QF_BV, solver_name='z3'):
    #Verify that the two interfaces are identical
    i0Ts, o0Ts = comb0.get_type()
    i1Ts, o1Ts = comb1.get_type()
    for i0, i1 in zip(i0Ts, i1Ts):
        assert i0.type == i1.type
    for o0, o1 in zip(o0Ts, o1Ts):
        assert o0.type == o1.type

    inputs = comb0.create_symbolic_inputs()
    o0 = _make_list(comb0.evaluate(*inputs))
    o1 = _make_list(comb1.evaluate(*inputs))

    formula = fc.And(o0_ == o1_ for o0_, o1_ in zip(o0, o1))

    not_formula = ~(formula.to_hwtypes())

    with smt.Solver(logic=logic, name=solver_name) as solver:
        solver.add_assertion(not_formula.value)
        res = solver.solve()
        if res is False:
            return None
        vals = {v.value: v.value.constant_value() for v in inputs}
        return vals
