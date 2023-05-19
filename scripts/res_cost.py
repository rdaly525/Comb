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

maxIR = 2
maxISA = 1
isa_name = 'cisc'
#consts = [0,1,-1]
if isa_name == 'ab':
    consts = []
    ir_kinds = ['BW', 'AR']
    all_costs = (
        [1, 1],
        [1, 5],
    )
elif isa_name == 'cmp':
    consts = [0,1]
    ir_kinds = ['C', 'CE', 'CU']
    all_costs = (
        [1, 1, 1, 1],
        [2, 4, 5, 1],
        #~, Z, C, N
    )
else:
    assert isa_name == 'cisc'
    consts = [0, 1]
    ir_kinds = ['C', 'AR', 'M']
    all_costs = (
        [1, 1, 1, 1, 1],
        [1, 2, 5, 4, 7],
        #neg, add, mul, add3, mac
    )
    #add:mul ~ 1: 2.5
    #neg:add ~ 1 : 2
log = False
print_rules = True
include_id = False
verbose = 0
N = 4

opMaxIR = None
opMaxISA = None
timeout = 12
res_dir = f"{dir}/../results/real"
dce = 1
cse = 0

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
solver_opts = SolverOpts(verbose=verbose, solver_name='z3', timeout=timeout, log=log)


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
cdb = []
for ci, costs in enumerate(all_costs):
    LC,E,CMP, C, K = (1,1,1,1,1)
    file = f"{res_dir}/res_cost_{N}_{isa_name}_{maxIR}_{maxISA}_{LC}{E}{CMP}{C}{K}_{timeout}"
    pfile = f"{file}.pickle"
    rfile = f"{file}.comb"

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
    ga = rd.gen_lowcost_rules(E_opts, ir_opts, narrow_opts, costs, solver_opts)
    for ri, rule in enumerate(ga):
        print("RULE", ri, flush=True)
        if print_rules:
            print(rule)
            print("*"*80)
        pass
    cdb.append(rd.rdb)

dba = cdb[0]
dbb = cdb[1]
overlap = 0
for (ka, _, ra) in dba.enum_rules():
    for (kb, _, rb) in dbb.enum_rules():
        if ka != kb:
            continue
        if ra.equal(rb):
            assert rb.equal(ra)
            overlap += 1

uniquea = dba.num_rules - overlap
uniqueb = dbb.num_rules - overlap
print(f"UA, UB, SAME = {uniquea}, {uniqueb}, {overlap}")











