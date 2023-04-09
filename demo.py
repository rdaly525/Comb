from comb.frontend.compiler import compile_program
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts
import os

dir_path = os.path.dirname(os.path.realpath(__file__))
am_file = f"{dir_path}/combs/addmul.comb"
sm_file = f"{dir_path}/combs/submul.comb"

with open(am_file, 'r') as f:
    am_obj = compile_program(f.read())
with open(sm_file, 'r') as f:
    sm_obj = compile_program(f.read())

N = 4
am_add = am_obj.get('am.add')
am_add.commutative = True
am_mul = am_obj.get('am.mul')
am_mul.commutative = True
sm_sub = sm_obj.get('sm.sub')
sm_sub.commutative = True
sm_mul = sm_obj.get('sm.mul')
sm_C = sm_obj.get('sm.C')
sm_mul.commutative = True



lhs = [
    am_mul[N],
    am_add[N],
]
rhs = [
    sm_mul[N],
    sm_sub[N],
    sm_C[N, 1],
]
maxL = 2
maxR = 3
ss = RuleDiscovery(lhs, rhs, maxL, maxR)
opts = SolverOpts(verbose=1, max_iters=1000, solver_name='z3')
rules = []
for ri, rule in enumerate(ss.gen_all(opts)):
    print("RULE", ri)
    print(rule)
    print("ENDRULE")
    rules.append(rule)
print("-"*80)
print("-"*80)
print("-"*80)
for ri, rule in enumerate(rules):
    print("RULE", ri)
    print(rule)
    print("ENDRULE")