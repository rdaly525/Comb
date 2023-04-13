#CEGIS: res SAT|UNSAT|MAX t (seconds)
#IOT:
import re

def parse_type(s):
    assert s[0] in 'CN'
    is_const = s[0]=='C'
    n = int(s[1:])
    return (n, is_const)

def parse_iot(s):
    m = re.match("\((.+)\) -> \((.+)\)", s)
    assert m is not None
    vs = [tuple(parse_type(v) for v in m.group(i).split(", ")) for i in (1, 2)]
    return vs[0], vs[1]

def parse_kind(s):
    m = re.match("\((.+)\) -> \((.+)\)", s)
    assert m is not None
    vs = [tuple(int(v) for v in m.group(i).split(", ")) for i in (1, 2)]
    return (vs[0], vs[1])

def parse_cegis(s):
    m = re.match("\((\w+), ([\w\.]+)\)", s)
    assert m is not None
    sat_res = m.group(1)
    assert sat_res in ('SAT', 'UNSAT', 'MAX')
    t = float(m.group(2))
    return (sat_res, t)

def parse_prepost(s):
    m = re.match("\((\d+), ([\d\.]+)\)", s)
    assert m is not None
    num_rules = int(m.group(1))
    t = float(m.group(2))
    return (num_rules, t)


def parse_line(l):
    m = re.match("(\w+): (.*)", l)
    if m is None:
        assert 0
    k = m.group(1)
    s = m.group(2)
    if k=='SYM':
        return (k,None)
    elif k=="KIND":
        l, r = parse_kind(s)
        return (k, (l,r))
    elif k=="CEGIS":
        sat, t = parse_cegis(s)
        return (k, (sat, t))
    elif k=='IOT':
        iT, oT = parse_iot(s)
        return (k, (iT, oT))
    elif k in ('PRE', 'POST'):
        r, t = parse_prepost(s)
        return (k, (r,t))
    assert 0

data = {}
syms = (
    #(0,0,0),
    (1,0,0),
    (0,1,0),
    #(0,0,1),
    (1,1,1),
)
for c, so, ip in syms:
    file = f"/Users/rdaly/comb/results/res{c}{so}{ip}.txt"
    try:
        with open(file, 'r') as f:
            smt_calls = {}
            state = None
            for l in f.readlines():
                k, d = parse_line(l)
                if k=="SYM":
                    state = 0
                elif state==0:
                    assert k=="KIND"
                    cur_kind = d
                    state = 1
                elif state==1:
                    if k=="KIND":
                        cur_kind = d
                        state = 1
                    elif k=="IOT":
                        cur_iot = d
                        smts = []
                        state = 2
                    elif k=='PRE':
                        pre = d
                        state = 1
                    elif k=='POST':
                        post = d
                    else:
                        print(k, d)
                        assert 0
                elif state==2:
                    assert k == "CEGIS"
                    sat_res, t = d
                    smts.append(d)
                    if sat_res in ("UNSAT", 'MAX'):
                        smt_calls[(cur_kind, cur_iot)] = smts
                        state = 1
                else:
                    assert 0
    except IOError:
        assert 0
    data[(c,so,ip)] = (pre, post, smt_calls)


q_info = {} #[query][sym]
sym_info = {} #[sym][query]
for sym, (pre, post, smt) in data.items():
    for query, results in smt.items():
        assert all([sat=="SAT" for sat,_ in results[:-1]])
        assert results[-1][0] in ("UNSAT", "MAX")
        num_calls = len(results)
        sat_time = sum(t for _,t in results[:-1])
        maxiter = results[-1][0] == "MAX"
        unsat_time = results[-1][1]
        longest = sorted(results, key=lambda v: v[1])[-1]
        q_info.setdefault(query,{})[sym] = (num_calls, sat_time, maxiter, unsat_time, longest)
        sym_info.setdefault(sym,{})[query] = (num_calls, sat_time, maxiter, unsat_time, longest)

for sym in syms:
    pre, post, _ = data[sym]
    pre_rules = pre[0]
    post_rules = post[0]
    synth_time = pre[1]
    num_calls = sum([data[0] for q, data in sym_info[sym].items()])
    sat_time = sum([data[1] for q, data in sym_info[sym].items()])
    num_max = sum([data[2] for q, data in sym_info[sym].items()])
    unsat_time = sum([data[3] for q, data in sym_info[sym].items()])
    longest = sorted([data[4] for q, data in sym_info[sym].items()],key=lambda v: v[1])[-1]
    print(sym)
    print(f'  rules: {pre_rules} -> {post_rules}')
    print('  synth_time', round(synth_time/60,2))
    print('  num_calls', num_calls)
    print('  sat_time', round(sat_time/60,2))
    print('  num_max', num_max)
    print('  unsat_time', round(unsat_time/60,2))
    print('  longest', longest)
