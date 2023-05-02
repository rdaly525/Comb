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
maxIR = 1
maxISA = 3
timeout = 5
ECK = (
    (0, 0, 0),
    #(0, 1, 0),
    #(0, 0, 1),
    (1, 0, 0),
    (1, 1, 1),
    #(1, 0, 1),
    #(1, 1, 0),
    #(0, 1, 1),
)

data = {}
for E, C, K in ECK:
    k = (E, C, K)
    file = f"{res_dir}/res{N}_{risc}_{maxIR}_{maxISA}_{E}{C}{K}_{timeout}.pickle"
    #file = f"{res_dir}/res{N}_{risc}_{num_ir}_{num_isa}_{maxIR}_{maxISA}_{E}{C}{K}_{timeout}.pickle"
    with open(file, 'rb') as f:
        v = pickle.load(f)
    ts = sorted([t for (n,t) in v['times']])
    cum = list(it.accumulate(ts))
    if E:
        et = v['enum']
        cum = [t+et for t in cum]
    data[k] = cum

names = {
    (0,0,0): "Incremental Exlusion",
    (1,0,0): "Rule Exclusion",
    (0,1,0): "Commutative Narrowing",
    (0,0,1): "Same-Inst Narrowing",
    (1,1,1): "Rule Exclusion and Narrowing",
}


fig = go.Figure()
for k, v in data.items():
    x = list(range(len(v)))
    print(len(v))
    y = v
    fig.add_scatter(x=x, y=y, mode='lines', name=names[k])
fig.update_layout(
    yaxis_title="Cummulative Time (s)",
    xaxis_title="Number of Unique Rules",
    title="Cactus",
)
fig.update_yaxes(type='log')
fig.update_layout(
    autosize=False,
    width=800,
    height=400,)
fig.show()