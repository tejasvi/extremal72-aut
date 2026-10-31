"""Greedy ordering simulation: how fast do syndrome spans grow vs constraints covered."""
import sys, math, time
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from forms import *
import numpy as np
n = 36
G = read_code36(39)
words = span(G)
ones = (1 << n) - 1
FS = FormSpace(G, n)
diag = [FS.functional(g, g) ^ FS.functional(g, ones) for g in G]

def shortened_basis(y):
    # Y_y: solve for combos c with (sum c_t G_t) & y == 0: linear map F2^18 -> F2^{supp y}
    supp = [i for i in range(n) if y >> i & 1]
    # matrix rows = basis vectors restricted to supp
    vecs = []
    for t, g in enumerate(G):
        r = 0
        for a, i in enumerate(supp):
            if g >> i & 1: r |= 1 << a
        vecs.append(r)
    # kernel of combination map
    ech = []  # (v, comb)
    kern = []
    for t, v in enumerate(vecs):
        comb = 1 << t
        for (r, rc) in ech:
            if v >> ((r & -r).bit_length() - 1) & 1:
                v ^= r; comb ^= rc
        if v:
            p = v & -v
            ech = [(r ^ v, rc ^ comb) if r & p else (r, rc) for (r, rc) in ech]
            ech.append((v, comb))
        else:
            kern.append(comb)
    out = []
    for comb in kern:
        x = 0
        for t in range(18):
            if comb >> t & 1: x ^= G[t]
        assert x & y == 0
        out.append(x)
    return out

def syndrome_of_e(e, xb):
    return sum((wt(e & x) & 1) << j for j, x in enumerate(xb))

low = [v for v in words if wt(v) in (8, 10, 12)]
info = {}
t0 = time.time()
for y in low:
    xb = shortened_basis(y)
    T = [i for i in range(n) if not y >> i & 1]
    w = wt(y)
    if w == 8:
        bad = {0} | {syndrome_of_e((1 << a) | (1 << b), xb) for ai, a in enumerate(T) for b in T[ai + 1:]}
    elif w == 10:
        bad = {syndrome_of_e(1 << a, xb) for a in T}
    else:
        bad = {0}
    info[y] = (xb, len(bad))
print("syndrome setup time", time.time() - t0)
from collections import Counter
for w in (8, 10, 12):
    c = Counter((len(info[y][0]), info[y][1]) for y in low if wt(y) == w)
    print("weight", w, "(dim Y_y, #bad syndromes):", dict(c))

# ---- greedy simulation ----
class Basis:
    def __init__(self):
        self.B = {}  # pivot -> vec (fully reduced)
    def red(self, v):
        for p, b in self.B.items():
            if v >> p & 1: v ^= b
        return v
    def add(self, v):
        v = self.red(v)
        if not v: return False
        p = v.bit_length() - 1
        for q in list(self.B):
            if self.B[q] >> p & 1: self.B[q] ^= v
        self.B[p] = v
        return True
    def rank_mod(self, vs):
        tmp = Basis(); tmp.B = {}
        r = 0
        for v in vs:
            v = self.red(v)
            for p, b in tmp.B.items():
                if v >> p & 1: v ^= b
            if v:
                p = v.bit_length() - 1
                for q in list(tmp.B):
                    if tmp.B[q] >> p & 1: tmp.B[q] ^= v
                tmp.B[p] = v; r += 1
        return r

funcs = {y: [FS.functional(y, x) for x in info[y][0]] for y in low}
logfrac = {}
for y in low:
    w = wt(y); d = len(info[y][0]) - 1
    logfrac[y] = math.log2((2 ** d - info[y][1]) / 2 ** d)
R = Basis()
for f in diag: R.add(f)
base = len(R.B)
W8 = [y for y in low if wt(y) == 8]
covered = set()
order = []
step = 0
while len(R.B) - base < 119:
    best = None
    for y in W8:
        if y in covered: continue
        r = R.rank_mod(funcs[y])
        if r == 0: covered.add(y); continue
        if best is None or r < best[0]: best = (r, y)
    r, y = best
    for f in funcs[y]: R.add(f)
    order.append(y)
    step += 1
    cov = [z for z in low if R.rank_mod(funcs[z]) == 0]
    lg = len(R.B) - base + sum(logfrac[z] for z in cov)
    cnt = Counter(wt(z) for z in cov)
    print(f"step {step:3d} r={r:2d} dim={len(R.B)-base:3d} covered w8={cnt[8]:3d} w10={cnt[10]:4d} w12={cnt[12]:5d}  log2est={lg:7.2f}", flush=True)
