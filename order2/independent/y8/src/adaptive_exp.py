"""Experiment: rep-specific U-part order (greedy by new dims and constraint strength given X) vs static k-first."""
import sys, pickle, math, time
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from problem import *
from engine_prep import *
from y8_struct import *
from linalg import Elim
P = Problem(read_code36(8), 36, 16)
S = structure(P.words)
FS = P.FS
Zc = [FS.functional(h, r) for h in S["Hb"] for r in S["Rb"]]
Bc = [FS.functional(h, S["vprime"]) for h in S["Hb"]]
Ac = [FS.functional(S["u0"], r) for r in S["Rb"]]
Xc = Zc + Bc + Ac
x = int(sys.argv[1], 16)
lam = float(sys.argv[2])
tag = sys.argv[3]
nd = len(P.diag)
EX = Elim()
for t, (f, c) in enumerate(P.diag): EX.add(f, 1 << t)
xv = []
for f in Xc:
    ok, _ = EX.add(f, 1 << (nd + len(xv)))
    if ok: xv.append(f)
assert len(xv) == 40
dconst = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
U8 = [y for y in P.low if y & ~(m18 | m2) == 0 and wt(y) == 8]
V8 = [y for y in P.low if y & ~(m16 | m2) == 0 and wt(y) == 8]
funcs = {y: [FS.functional(y, xx) for xx in P.shortened_basis(y)] for y in P.low}
# strength of U-word y given X: functionals reduced modulo [diag | X]; the X-determined part fixes some syndrome
# coordinates; allowed fraction = (#non-forbidden syndromes consistent with the fixed part) / (#consistent syndromes)
def strength(y):
    xb = P.shortened_basis(y)
    forb = P.forbidden_syndromes(y, xb)
    fixed = []  # (j-combination mask, value) relations: a combination of syndrome coords that is X-determined
    # find all combinations c (over m coords) whose functional lies in span(diag, X): kernel computation
    m = len(xb)
    E = Elim(); E.rows = dict(EX.rows)
    rel = []
    # brute force over combinations is 2^m; m <= 11 -> fine
    for cmask in range(1, 1 << m):
        f = 0
        for j in range(m):
            if cmask >> j & 1: f ^= funcs[y][j]
        combo, resid = E.express(f)
        if resid == 0:
            val = (bin(combo & dconst & ((1 << nd) - 1)).count("1") + bin((combo >> nd) & x).count("1")) & 1
            rel.append((cmask, val))
    cons = [s for s in range(1 << m) if all((bin(s & cm).count("1") & 1) == v for cm, v in rel)]
    allowed = [s for s in cons if s not in forb]
    return len(allowed) / len(cons)
t0 = time.time()
st = {y: strength(y) for y in U8}
print("strength computed in %.1f s; min %.3f, distribution:" % (time.time() - t0, min(st.values())),
      sorted(round(v, 2) for v in st.values())[:10], "...")
def newdims(E, y):
    tmp = Elim(); tmp.rows = dict(E.rows)
    return sum(tmp.add(f, 0)[0] for f in funcs[y])
E = Elim()
for f, c in P.diag: E.add(f, 0)
for f in Xc: E.add(f, 0)
order, rem = [], list(U8)
while rem:
    y = min(rem, key=lambda y: (newdims(E, y) + lam * math.log2(max(st[y], 1e-9)), y))
    for f in funcs[y]: E.add(f, 0)
    order.append(y); rem.remove(y)
def greedy(E, words):
    o, rem = [], list(words)
    while rem:
        y = min(rem, key=lambda y: (newdims(E, y), wt(y), y))
        for f in funcs[y]: E.add(f, 0)
        o.append(y); rem.remove(y)
    return o
order += greedy(E, V8)
seen = set(order)
order += sorted([y for y in P.low if y not in seen], key=lambda y: (wt(y), y))
ED = EngineData(P, order, extra_var_funcs=Xc)
ED.write("<HOME>/c72_indep/y8/tmp/adapt_%s.eng" % tag)
print("first words strength:", [round(st[y], 3) for y in order[:8]])
