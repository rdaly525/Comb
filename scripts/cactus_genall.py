import pickle
import itertools as it
import os

dir = os.path.dirname(os.path.realpath(__file__))
res_dir = f"{dir}/../results/real"
import plotly.express as px
import plotly.graph_objects as go
#consts = [0]
#ir_kinds = ['C', 'BW', 'CMP', 'AR']
# The above was used for the 1->3

log_plot = True
isa_name = 'cmp'
#isa_name = 'ab'
isa_name = 'cisc'
N = 4
maxIR = 3
maxISA = 2
timeout = 12
LC_test = 1
#LC,E,CMP,C,K
lc_params = (
    (1,1,1,1,1),
    #(1,1,0,1,1),
    (0,1,1,1,1),
    #(0,0,1,0,0),
    #(0,0,0,1,0),
    #(0,0,0,0,1),
    #(0,0,0,0,0),
)
all_params = (
    (0,0,0,0,0),
    #(0,0,0,0,1),
    #(0,0,0,1,0),
    #(0,1,0,0,0),
    #(0,1,1,0,0),
    (0,1,1,1,1),
)
params = lc_params if LC_test else all_params

data = {}
for LC,E,CMP, C, K in params:
#for E, CMP, C, K in ECK:
    opts = (LC, E, CMP, C, K)
    #file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{LC_test}_{LC}{E}{CMP}{C}{K}_{timeout}.pickle"
    #file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{E}{CMP}{C}{K}_{timeout}.pickle"
    #file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{LC}{E}{CMP}{C}{K}_{timeout}.pickle"
    file = f"{res_dir}/res{N}_{isa_name}_{maxIR}_{maxISA}_{LC_test}_{LC}{E}{CMP}{C}{K}_{timeout}.pickle"
    with open(file, 'rb') as f:
        v = pickle.load(f)
    mn_info = v['mn']
    print("MN LC")
    for mn, cnt in mn_info.items():
        print(mn, cnt)

    print(opts)
    t_info = v['t']
    dps = []
    mn_cnt = {}
    for (lids, rids, NI), info in t_info.items():
        mn = (len(lids),len(rids))
        mn_cnt[mn] = mn_cnt.get(mn, 0) + info['u'] + info['e']
        n = info['u']
        if n==0:
            n+=.000001
        st = info['st']
        et = info['et']
        dps.append((n, st+et))
    for (m,n), cnt in mn_cnt.items():
        print(f"{m},{n} -> {cnt}")
    print("tot", sum(mn_cnt.values()))
    dps = sorted(dps, key=lambda dp: dp[1]/dp[0])
    cum = [(0,0.001)]
    for cn, ct in dps:
        pn, pt = cum[-1]
        cum.append((cn+pn,ct+pt))

    data[opts] = cum

if LC_test:
    x = data[(0,1,1,1,1)][-1][1]
else:
    x = data[(0,0,0,0,0)][-1][1]

for k in params:
    print(k, (x/data[k][-1][1]))

names = {
    (0,0,0,0,0): "Incremental solve",
    (0,1,0,0,0): "Dup Exclusion",
    (0,1,1,0,0): "Dup + Comp Exclusion",
    (0,0,0,1,0): "Commutative Narrowing",
    (0,0,0,0,1): "Same-Inst Narrowing",
    (0,1,1,1,1): "Dup + Comp Exclusion + Narrowing",
    (1,1,1,1,1): "Low Cost Composite and Duplicate Exclusion",
    (1,1,0,1,1): "Low Cost Duplicate Exclusion",
}


fig = go.Figure()
c = ['red', 'blue', 'green', 'orange', 'purple', 'black']
for i, (k, v) in enumerate(data.items()):
    x = [n for n,_ in v]
    y = [t/60 for _,t in v]
    #fig.add_scatter(x=x, y=y, mode='lines+markers', name=names[k])
    fig.add_scatter(x=x, y=y, mode='lines', name=names[k], line=dict(color=c[i]))
    v = fig.add_scatter(
        x=[x[-1]],
        y=[y[-1]],
        mode='markers',
        line=dict(color=c[i]),
        marker_symbol='circle-dot',
        marker_size=12,
    )
    fig['data'][-1]['showlegend']=False

if LC_test:
    xtit = "Number of Lowest Cost Rules"
else:
    xtit = "Number of Unique Rules"

fig.update_layout(
    yaxis_title="Cummulative SAT Time (min)",
    xaxis_title=xtit,
    title="Cactus",
)
s = 100
if log_plot:
    fig.update_yaxes(type='log')
fig.update_layout(
    autosize=False,
    width=8*s,
    height=5*s,
)
#fig.show()