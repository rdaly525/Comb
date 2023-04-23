import pickle
import itertools as it
res_dir = "/Users/rdaly/Comb/results/small"
import plotly.express as px
import plotly.graph_objects as go

to = 10
maxIR, maxISA = 2,3
data = {}
for E, c, so, ip in (
    (1,1,1,1),
    (1,0,0,1),
    (1,0,1,0),
    (1,1,0,0),
    (1,0,0,0),
    #(1,1,1,0),
    #(1,1,0,1),
    #(0,0,1),
    #(0,1,0),
    #(1,0,0),
    #(0,0,0),
):
    k = (E, c, so, ip)
    file = f"{res_dir}/res{maxIR}_{maxISA}_{E}{c}{so}{ip}_{to}.pickle"
    with open(file, 'rb') as f:
        v = pickle.load(f)
    ts = sorted([t for (n,t) in v['times']])
    cum = list(it.accumulate(ts))
    data[k] = cum

fig = go.Figure()
for k, v in data.items():
    x = list(range(len(v)))
    print(len(v))
    y = v
    fig.add_scatter(x=x, y=y, mode='lines', name=str(k))
fig.update_layout(
    yaxis_title="Cummulative Time (s)",
    xaxis_title="Number of unique rules",
    title="Cactus",
)
#fig.update_yaxes(type='log')
fig.show()