import pickle
import itertools as it
import os

dir = os.path.dirname(os.path.realpath(__file__))
res_dir = f"{dir}/../results/small"
import plotly.express as px
import plotly.graph_objects as go
#consts = [0]
#ir_kinds = ['C', 'BW', 'CMP', 'AR']
# The above was used for the 1->3


risc = 1
N = 4
maxIR = 2
maxISA = 2
timeout = 5
LC_test = 1
#LC,E,CMP,C,K
lc_params = (
    (0,1,1,1,1),
    (1,1,0,1,1),
    (1,1,1,1,1),
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

data = {}
for LC,E,CMP, C, K in params:
#for E, CMP, C, K in ECK:
    opts = (LC, E, CMP, C, K)
    #file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{LC}{E}{CMP}{C}{K}_{timeout}.pickle"
    file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{LC_test}_{LC}{E}{CMP}{C}{K}_{timeout}.pickle"
    #file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{E}{CMP}{C}{K}_{timeout}.pickle"
    with open(file, 'rb') as f:
        v = pickle.load(f)
    mn_info = v['mn']
    print(opts)
    for (m,n), cnt in mn_info.items():
        print(f"{m},{n} -> {cnt}")
    t_info = v['t']
    dps = []
    for k, info in t_info.items():
        n = info['u']
        if n==0:
            n+=.001
        st = info['st']
        et = info['et']
        dps.append((n, st+et))

    dps = sorted(dps, key=lambda dp: dp[1]/dp[0])
    cum = [(0,0.001)]
    for cn, ct in dps:
        pn, pt = cum[-1]
        cum.append((cn+pn,ct+pt))

    data[opts] = cum

#x = data[(0,0,0,0)][-1][1]
x = data[(0,1,1,1,1)][-1][1]

for k in params:
    print(k, (x/data[k][-1][1]))

names = {
    (0,0,0,0,0): "Incremental Exlusion",
    (0,1,0,0,0): "Duplicate Exclusion",
    (0,1,1,0,0): "Composite Exclusion",
    (0,0,0,1,0): "Commutative Narrowing",
    (0,0,0,0,1): "Same-Inst Narrowing",
    (0,1,1,1,1): "Composite Exclusion and Narrowing",
    (1,1,1,1,1): "Low Cost Composite and Duplicate Exclusion",
    (1,1,0,1,1): "Low Cost Duplicate Exclusion",
}


fig = go.Figure()
c = ['red', 'blue', 'green']
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
fig.update_layout(
    yaxis_title="Cummulative Time (min)",
    xaxis_title="Number of Unique Rules",
    title="Cactus",
)
#fig.update_yaxes(type='log')
fig.update_layout(
    autosize=False,
    width=800,
    height=600,
)
fig.show()