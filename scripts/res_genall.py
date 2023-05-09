#This is a script for comparing synth time for duplicates.

import os
from comb.frontend.compiler import compile_program
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts
from timeit import default_timer as time

dir = os.path.dirname(os.path.realpath(__file__))
ir_fname = f"{dir}/combs/ir.comb"
irK = {}
with open(ir_fname, 'r') as f:
    obj = compile_program(f.read())
    irK['C'] = obj.get_from_ns('irC')[0]
    irK['BW'] = obj.get_from_ns('irBW')
    irK['CE'] = obj.get_from_ns('irCE')
    irK['CS'] = obj.get_from_ns('irCS')
    irK['CU'] = obj.get_from_ns('irCU')
    irK['AR'] = obj.get_from_ns('irAR')
    irK['M'] = obj.get_from_ns('irM')

dce = 1
cse = 0
#consts = [0,1,-1]
consts = [0]
#ir_kinds = ['C', 'BW', 'CE', 'CU', 'CS', 'AR', 'M']
ir_kinds = ['CS']
#ir_kinds = ['CMP']
#id, nand sub, ~, Z, C, N, V
#costs = [1, 5, 25, 2, 26, 26, 26, 26]
costs = [50, 50, 50, 1, 3, 50, 3, 3]
#costs = [1, 1, 1, 1, 1]
log = False
print_rules = True
include_id = False
verbose = 1
risc = 1
N = 4
maxIR = 1
maxISA = 4
opMaxIR = None
opMaxISA = None
timeout = 20
res_dir = f"{dir}/../results/small"
LC_test = 1
#LC,E,CMP,C,K
lc_params = (
    (1,1,1,1,1),
    #(1,1,0,1,1),
    #(0,1,1,1,1),
    #(0,0,1,0,0),
    #(0,0,0,1,0),
    #(0,0,0,0,1),
    #(0,0,0,0,0),
)
all_params = (
    (0,1,1,1,1),
    (0,1,1,0,0),
    (0,0,1,0,0),
    (0,0,0,1,0),
    (0,0,0,0,1),
    (0,0,0,0,0),
)

params = lc_params if LC_test else all_params
ir = []
for k in ir_kinds:
    if k=='C':
        ir.extend(irK[k][N, c] for c in consts)
    else:
        ir.extend([inst[N] for inst in irK[k]])
if risc:
    isa_fname = f"{dir}/combs/isa_risc.comb"
else:
    isa_fname = f"{dir}/combs/isa_cisc.comb"
with open(isa_fname, 'r') as f:
    obj = compile_program(f.read())
isa = [c[N] for c in obj.get_from_ns("isa")]
if not include_id:
    isa = isa[1:]
    costs = costs[1:]
solver_opts = SolverOpts(verbose=verbose, solver_name='z3', timeout=timeout, log=log)
for LC,E,CMP, C, K in params:
    if not LC_test:
        assert not LC
    print("F:", LC_test, LC, E, CMP, C, K)
    file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{LC_test}_{LC}{E}{CMP}{C}{K}_{timeout}"
    pfile = f"{file}.pickle"
    rfile = f"{file}.comb"
    #sym_opts = SymOpts(comm=c, same_op=so, input_perm=False)

    start_time = time()
    rd = RuleDiscovery(
        lhss=ir,
        rhss=isa,
        maxL=maxIR,
        maxR=maxISA,
        opMaxL=opMaxIR,
        opMaxR=opMaxISA,
    )
    ir_opts = (dce, cse)
    narrow_opts = (C, K)
    E_opts = (LC, E, CMP)
    if LC_test:
        ga = rd.gen_lowcost_rules(E_opts, ir_opts, narrow_opts, costs, solver_opts)
    else:
        ga = rd.gen_all_rules(E_opts, ir_opts, narrow_opts, solver_opts)
    for ri, rule in enumerate(ga):
        print("RULE", ri, flush=True)
        if print_rules:
            print(rule)
            print("*"*80)
        pass
    db = rd.rdb
    for k, info in db.time_info.items():
        num_unique = info["u"]
        extra = info['e']
        sat_time = info['st']
        extra_time = info['et']
        assert extra >=0
        print(f"KIND:{k}, UNIQUE:{num_unique}, DUP: {extra}, ST: {sat_time}, ET: {extra_time}")
    db.pickle_info(pfile)