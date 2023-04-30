import pickle
import itertools as it
res_dir = "/Users/rdaly/Comb/results/small"
import plotly.express as px
import plotly.graph_objects as go

to = 10
maxIR, maxISA = 3,3
c, so, ip = 1, 0, 0
file = f"{res_dir}/Eres{maxIR}_{maxISA}_{c}{so}{ip}_{to}.pickle"
with open(file, 'rb') as f:
    v = pickle.load(f)
scale = 60
e_t = sorted([sum(ts)/scale for ts in v['e']])
ne_t = sorted([sum(ts)/scale for ts in v['ne']])
nee_t = sum([sum(ts) for ts in v['nee']])/scale
nee_t = 0
e_cum = list(it.accumulate(e_t))
ne_cum = [nee_t + t for t in it.accumulate(ne_t)]

data = {
    "High Cost Exclusion":e_cum,
    "No Exclusion":ne_cum,
}

fig = go.Figure()
for k, v in data.items():
    x = list(range(len(v)))
    y = v
    fig.add_scatter(x=x, y=y, mode='lines', name=str(k))
fig.update_layout(
    yaxis_title="Cumulative Time (min)",
    xaxis_title="Number of Synthesized Rules",
    title="Cactus",
)
fig.update_yaxes(type='log')
fig.update_layout(
    autosize=False,
    width=800,
    height=400,)
fig.show()