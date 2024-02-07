from comb.synth.pattern import Pattern, PatternMatcher, SymOpts
from typing import List
import hwtypes as ht
import hwtypes.smt_utils as fc
from comb.synth.solver_utils import SolverOpts, get_var
from pysmt import shortcuts as smt
from comb.frontend.ir import CombSpecialized
from comb.frontend.stdlib import CBVConst

class InstructionSel:
    def run(self, max_cost = None):
        raise NotImplementedError()

class OptimalInstructionSel(InstructionSel):
    def __init__(self, pat: Pattern, rules, symops: SymOpts, solverops: SolverOpts):
        self.pat = pat
        self.rules = rules
        self.symops = symops
        self.solverops = solverops
        self.matches = None
        

    def run(self, max_cost = None):
        if self.matches is None:
            self.matches = [PatternMatcher(rule.lhs, self.pat, self.symops).match_all() for rule in self.rules] 

        #keep track of the SMT bools associated with each output
        node_o = {}
        cost = ht.SMTBitVector[32](0)

        implications = []

        for ri, (rule, matches) in enumerate(zip(self.rules, self.matches)):
            #only really need to know IO locations of matches in the pat
            #many matches will likely have the same IO
            matches_io = dict()
            for mi, match in enumerate(matches):
                matches_i = set()
                matches_o = set()

                for k,v in match.forall_map.items():
                    if k[0] == -1:
                        matches_i.add(v)

                for (srci, srca),_ in rule.lhs.out_edges:
                    matches_o.add((match.opi_map[srci], srca))

                matches_i, matches_o = frozenset(matches_i), frozenset(matches_o)
                if (matches_i, matches_o) not in matches_io:
                    matches_io[(matches_i, matches_o)] = mi

            #now we go through the minimal set of matches
            for (matches_i, matches_o), mi in matches_io.items():
                use_this_tile = get_var(f"tile({ri},{mi})", 0)
                cost = use_this_tile.ite(cost + ht.SMTBitVector[32](rule.cost), cost)
                for o in matches_o:
                    node_o.setdefault(o, []).append(use_this_tile)

                implications.append((use_this_tile, matches_i))
            
        # inputs to the pat are available
        for i in range(self.pat.NI):
            node_o[(-1,i)] = [ht.SMTBit(1)]

        #constants are available
        for i,op in enumerate(self.pat.ops):
            if isinstance(op, CombSpecialized) and isinstance(op.comb, CBVConst):
                node_o[(i,0)] = [ht.SMTBit(1)]
        
        if max_cost is not None:
            assert max_cost >= 0
            cost_cond = cost <= max_cost
        else:
            cost_cond = ht.SMTBit(1)
        output_cond = []
        for src,_ in self.pat.out_edges:
            output_cond.append(fc.Or(node_o.setdefault(src, [ht.SMTBit(0)])))

        inputs_available_cond = []
        for tile_used, inputs in implications:
            inputs_available = fc.And([fc.Or(node_o.setdefault(i, [ht.SMTBit(0)])) for i in inputs])
            inputs_available_cond.append(fc.Implies(tile_used, inputs_available))

        f = fc.And([cost_cond, fc.And(output_cond), fc.And(inputs_available_cond)]).to_hwtypes().value
        with smt.Solver(logic=self.solverops.logic, name=self.solverops.solver_name) as solver:
            solver.add_assertion(f)
            return solver.solve()


            


            


                
            

                 
                

    

