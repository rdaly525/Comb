#This is a script for comparing synth time for duplicates.

import os
from comb.frontend.compiler import compile_program
from comb.synth.rule_discover import RuleDiscovery
from comb.synth.solver_utils import SolverOpts
from timeit import default_timer as time

from comb.synth.verify import verify

dir = os.path.dirname(os.path.realpath(__file__))
ir_fname = f"{dir}/combs/ir.comb"
irK = {}
with open(ir_fname, 'r') as f:
    ir_obj = compile_program(f.read())
    irK['C'] = ir_obj.get_from_ns('irC')[0]
    irK['BW'] = ir_obj.get_from_ns('irBW')
    irK['CE'] = ir_obj.get_from_ns('irCE')
    irK['CS'] = ir_obj.get_from_ns('irCS')
    irK['CU'] = ir_obj.get_from_ns('irCU')
    irK['AR'] = ir_obj.get_from_ns('irAR')
    irK['M'] = ir_obj.get_from_ns('irM')

dce = 1
cse = 0
#consts = [0,1,-1]
consts = [0,1]
#ir_kinds = ['C', 'BW', 'CE', 'CU', 'CS', 'AR', 'M']
#ir_kinds = ['CE', 'CS', 'CU']
ir_kinds = ['C', 'CE', 'CU']
#ir_kinds = ['CMP']
#id, nand sub, ~, Z, C, N, V
#costs = [1, 5, 25, 2, 26, 26, 26, 26]
#costs = [50, 50, 50, 1, 1, 50, 1, 1]
costs = [1, 1, 1, 1]
log = False
print_rules = True
include_id = False
verbose = 0
isa_name = 'cmp'
N = 4
maxIR = 2
maxISA = 2
opMaxIR = None
opMaxISA = None
timeout = 12
res_dir = f"{dir}/../results/real"
LC_test = 0
#LC,E,CMP,C,K
lc_params = (
    (1,1,1,1,1),
    (1,1,0,1,1),
    (0,1,1,1,1),
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
isa_fname = f"{dir}/combs/isa_{isa_name}.comb"
with open(isa_fname, 'r') as f:
    isa_obj = compile_program(f.read())
isa = [c[N] for c in isa_obj.get_from_ns("isa")]
solver_opts = SolverOpts(verbose=verbose, solver_name='btor', timeout=timeout, log=log)


#slt_file = '''
#Comb t.slt
#Param N: Int
#In x: BV[N]
#In y: BV[N]
#Out o: BV[N]
#n = isa.cmp_N[N](x,y)
#v = isa.cmp_V[N](x,y)
#eq = isa.cmp_Z[N](n,v)
#o = isa.flag_nand[N](eq,eq)
#'''
##
#obj = compile_program(slt_file, [isa_obj])
#sge = obj.get('t','slt')[N]
#print(sge)
#ir_sge = ir_obj.get('irCS', 'bvslt')[N]
#ce = verify(sge, ir_sge, solver_opts)
#print(ce)
#assert ce is None
#assert 0


for LC,E,CMP, C, K in params:
    if not LC_test:
        assert not LC
    print("F:", LC_test, LC, E, CMP, C, K)
    file = f"{res_dir}/res{N}_{isa_name}_{maxIR}_{maxISA}_{LC_test}_{LC}{E}{CMP}{C}{K}_{timeout}"
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
    print("TOTTIME",time()-start_time)
