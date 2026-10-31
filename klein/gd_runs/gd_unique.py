"""Unique node counts of the guess-and-determine (third solver) runs.
Selection as in v4status.py (out2 for OLD tasks in wide_status.txt; test/w14_* for 0_0).
Per part: DONE line (nodes, split=S, part p/P) and 'hist:' line (depth:count).
Unique per instance = sum_{d<=S} hist (identical in all parts; checked) + sum over parts of sum_{d>S} hist."""
import os, re, glob, sys
base = sys.argv[1]
old = set()
for l in open(os.path.join(base, 'wide_status.txt')):
    t, i, p = l.split()
    if t == 'OLD': old.add((i, int(p)))
insts = sorted(set(re.sub(r'v4_(\d+_\d+)_\d+\.out', r'\1', os.path.basename(f)) for f in glob.glob(os.path.join(base, 'out', 'v4_*_*_*.out'))) | {'0_0'})
def parse(f):
    done = None; hist = None
    try:
        for l in open(f):
            if l.startswith('DONE result=COMPLETE'): done = l
            elif l.startswith('hist:'): hist = {int(a): int(b) for a, b in (x.split(':') for x in l.split()[1:])}
    except FileNotFoundError:
        return None
    if done is None or hist is None: return None
    m = re.search(r'nodes (\d+) sols (\d+) .*split=(\d+) part (\d+)/(\d+)', done)
    return dict(nodes=int(m.group(1)), sols=int(m.group(2)), split=int(m.group(3)), part=int(m.group(4)), npart=int(m.group(5)), hist=hist)
tot_sum = 0; tot_unique = 0; ncomplete = 0; incomplete = []; nsols = 0; mism = 0; histsum_ok = True
per = {}
for i in insts:
    if i == '0_0':
        files = [os.path.join(base, 'test', f'w14_{p}.out') for p in range(64)]
    else:
        files = [os.path.join(base, 'out2' if (i, p) in old else 'out', f'v4_{i}_{p}.out') for p in range(16)]
    parts = [parse(f) for f in files]
    if not all(parts):
        incomplete.append(i); continue
    ncomplete += 1
    S = parts[0]['split']
    up = {d: c for d, c in parts[0]['hist'].items() if d <= S}
    for q in parts:
        assert q['split'] == S and q['npart'] == len(parts)
        if {d: c for d, c in q['hist'].items() if d <= S} != up: mism += 1
        if sum(q['hist'].values()) != q['nodes']: histsum_ok = False
        nsols += q['sols']
    s = sum(q['nodes'] for q in parts)
    u = sum(up.values()) + sum(c for q in parts for d, c in q['hist'].items() if d > S)
    tot_sum += s; tot_unique += u; per[i] = (s, u)
print('instances', len(insts), 'complete', ncomplete, 'incomplete', incomplete)
print('sum of DONE nodes over parts (as v4status/totals):', tot_sum)
print('unique nodes:', tot_unique, '(%.6e)' % tot_unique)
print('solutions:', nsols, ' parts with differing upper histogram:', mism, ' hist sums equal DONE nodes:', histsum_ok)
big = sorted(per.items(), key=lambda kv: -kv[1][1])[:5]
print('largest by unique:', big)
print('instances where sum != unique:', sum(1 for s, u in per.values() if s != u))
