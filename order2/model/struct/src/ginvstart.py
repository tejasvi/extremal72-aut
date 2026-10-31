"""Candidate G-invariant starting subspaces W* (spans of Aut(Y)-orbits of low words and sums of two such spans,
dim <= DMAX), each with a basis of low words ordered by max new pruning.  Prints one line per candidate:
'CAND dim orbits(sizes/weights) prefix(36-bit words comma-separated)'.  Usage: ginvstart.py CI [DMAX]"""
import sys, pickle, itertools
import numpy as np
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from common import *
ci = int(sys.argv[1]); DMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 7
codes = load(); Yg = codes[ci]
res = pickle.load(open('<HOME>/c72/c2opt/struct/inst/invs.pkl', 'rb'))
gens = res[ci]['perms']
W = span_np(Yg); widx = {int(x): u for u, x in enumerate(W.tolist())}
def ap(perm, w):
    o = 0
    while w:
        b = w & -w; i = b.bit_length() - 1; o |= 1 << perm[i]; w ^= b
    return o
wl = np.zeros(1 << 18)
for l in open(f'<HOME>/c72/c2opt/struct/inst/data/low_{ci}.txt'):
    y, x = l.split(); wl[widx[int(y)]] = float(x)
lowu = np.nonzero(wl)[0].tolist()
orbits = []; done = set()
for u0 in lowu:
    if u0 in done: continue
    y0 = int(W[u0]); orb = {y0}; fr = [y0]
    while fr:
        nf = []
        for v in fr:
            for g in gens:
                x = ap(g, v)
                if x not in orb: orb.add(x); nf.append(x)
        fr = nf
    us = sorted(widx[x] for x in orb); done |= set(us); orbits.append(us)
def span_of(us):
    sp = np.array([0], dtype=np.int64); basis = []
    for u in us:
        if not (sp == u).any():
            basis.append(u); sp = np.concatenate([sp, sp ^ u])
    return sp, basis
cands = []
spans = []
for oi, o in enumerate(orbits):
    sp, b = span_of(o)
    if len(b) <= DMAX: spans.append((oi, sp, len(b)))
for oi, sp, dd in spans: cands.append(((oi,), sp, dd))
for (o1, s1, d1), (o2, s2, d2) in itertools.combinations(spans, 2):
    if d1 + d2 > DMAX + 3: continue
    sp, b = span_of(sorted(set(s1.tolist()) | set(s2.tolist())))
    if len(b) <= DMAX and len(b) > max(d1, d2): cands.append(((o1, o2), sp, len(b)))
seen = set(); out = []
for key, sp, dd in cands:
    fs = frozenset(sp.tolist())
    if fs in seen: continue
    seen.add(fs)
    lows = [u for u in sp.tolist() if wl[u] > 0]
    # internal order: greedy by new pruning, only low words of W*
    B = []; cur = np.array([0], dtype=np.int64)
    while len(B) < dd:
        best = None
        for c in lows:
            if (cur == c).any(): continue
            gain = wl[cur ^ c].sum()
            if best is None or gain > best[0]: best = (gain, c)
        B.append(best[1]); cur = np.concatenate([cur, cur ^ best[1]])
    L = wl[sp].sum()
    desc = '+'.join(f"{len(orbits[o])}w{pc(int(W[orbits[o][0]]))}" for o in key)
    out.append((dd, -L, desc, B))
out.sort()
for dd, mL, desc, B in out:
    print(f"CAND {dd} {desc} L={-mL:.1f} " + ','.join(str(int(W[b])) for b in B))
