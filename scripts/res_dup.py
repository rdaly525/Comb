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
    irK['CMP'] = obj.get_from_ns('irCMP')
    irK['AR'] = obj.get_from_ns('irAR')
    irK['M'] = obj.get_from_ns('irM')

dce = 1
cse = 0
#consts = [0,1,-1]
consts = [0]
#ir_kinds = ['C', 'BW', 'CMP', 'AR', 'M']
ir_kinds = ['C', 'BW', 'CMP', 'AR']
log = False
print_rules = False
verbose = 0
risc = 1
N = 4
maxIR = 1
maxISA = 3
opMaxIR = None
opMaxISA = None
timeout = 5
res_dir = f"{dir}/../results/small"
ECK = (
    (1, 1, 1),
    #(1, 0, 1),
    #(1, 1, 0),
    (1, 0, 0),
    (0, 0, 0),
    #(0, 1, 1),
    (0, 0, 1),
    (0, 1, 0),
)




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
solver_opts = SolverOpts(verbose=verbose, solver_name='z3', timeout=timeout, log=log)
print("IR,ISA", len(ir), len(isa))
for E, C, K in ECK:
    print("F:", E, C, K)
    irk_str = "$".join(ir_kinds)
    file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{E}{C}{K}_{timeout}"
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
    ga = rd.gen_all_rules(E, ir_opts, narrow_opts, solver_opts)
    for ri, rule in enumerate(ga):
        if print_rules:
            print("RULE", ri, flush=True)
            print(rule)
            print("*"*80)
        pass
    db = rd.rdb
    ts = db.time_info['times']
    et = db.time_info['enum']
    print("TIMES", et)
    for ti, t in enumerate(ts):
        print(ti, t[0], t[1])
    rd.rdb.pickle_time(pfile)
    for m2n, cnt in rd.rdb.get_m2n().items():
        print(m2n, cnt)