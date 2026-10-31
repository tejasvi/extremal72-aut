"""Control for the C2 x C2 model at length 48: QR48 has a free V4 action (PSL(2,47), 47 = 3 mod 4 so involutions
are fixed-point-free).  Build Y = pi(C(alpha)), bb = action of beta on alpha-pairs (positions preserved), extract
QR48's own form B, check invariance / diagonal / good classes, then run the V4 guess-and-determine solver and CMS."""
import sys, time, itertools, os
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
sys.path.insert(0, HERE); sys.path.insert(0, HERE)
sys.path.insert(0, HERE)
from codes import qr48_gens, span_np, psl2_47_perms
from v4sat import setup, solve, pc
N = 48
gens = psl2_47_perms()
# enumerate PSL(2,47) as permutations of 48 points
idp = tuple(range(N)); seen = {idp}; fr = [idp]
while fr:
    nf = []
    for p in fr:
        for g in gens:
            q = tuple(g[p[i]] for i in range(N))
            if q not in seen: seen.add(q); nf.append(q)
    fr = nf
G = list(seen); print("group order", len(G))
invs = [p for p in G if p != idp and all(p[p[i]] == i for i in range(N))]
print("involutions", len(invs), "all fpf:", all(all(p[i] != i for i in range(N)) for p in invs))
alpha = invs[0]
beta = next(p for p in invs if p != alpha and all(alpha[p[i]] == p[alpha[i]] for i in range(N)))
W = span_np(qr48_gens()); Wl = [int(x) for x in W]; Wset = set(Wl)
def ap(perm, w):
    o = 0
    for i in range(N):
        if (w >> i) & 1: o |= 1 << perm[i]
    return o
basisC = [int(x) for x in qr48_gens()]
assert all(ap(alpha, g) in Wset and ap(beta, g) in Wset for g in basisC)
# pairs and labelling: pair i = (p_i, alpha p_i); for beta-orbits {i, j}: pair j = (beta p_i, beta alpha p_i)
pairs = []; used = set()
for p in range(N):
    if p in used: continue
    q = beta[p]
    pairs.append((p, alpha[p])); pairs.append((q, alpha[q]))
    used |= {p, alpha[p], q, alpha[q]}
m = len(pairs); assert m == 24
pidx = {}
for i, (a, b) in enumerate(pairs): pidx[a] = (i, 0); pidx[b] = (i, 1)
bb = [pidx[beta[pairs[i][0]]][0] for i in range(m)]
assert all(pidx[beta[pairs[i][0]]][1] == 0 and pidx[beta[pairs[i][1]]][1] == 1 for i in range(m))
# Y = pi(C(alpha)); also y-map v -> (a_i + b_i), z = a
fixed = [w for w in Wl if ap(alpha, w) == w]
def proj(w):
    y = 0; z = 0
    for i, (a, b) in enumerate(pairs):
        ai = (w >> a) & 1; bi = (w >> b) & 1
        if ai ^ bi: y |= 1 << i
        if ai: z |= 1 << i
    return y, z
Ywords = set(proj(w)[1] for w in fixed)
print("|Y| =", len(Ywords), " d(Y) =", min(pc(y) for y in Ywords if y))
# generators of Y
Ygens = []; red = []
for y in sorted(Ywords):
    r = y
    for b in red: r = min(r, r ^ b)
    if r: Ygens.append(y); red.append(r)
assert len(Ygens) == 12
S = setup(Ygens, bb, verbose=True, m=24, d=12)
# QR48's own B in the setup's basis: B(b_k, b_l) = <z(b_k), b_l> where z(b_k) is the z-part of a codeword with y = b_k
zof = {}
for w in Wl:
    y, z = proj(w)
    if y not in zof: zof[y] = z
basis = S['basis']
Bq = {}
for (i, j) in S['E']:
    Bq[(i, j)] = pc(zof[basis[i]] & basis[j]) & 1
inv_ok = all(Bq[(min(a, b), max(a, b))] == Bq[(min(i, j), max(i, j))] for (i, j) in S['E']
             for (a, b) in [(None, None)] if False) or True
print("QR48 form extracted; checking it satisfies the model constraints via the solver's affine description")
# express Bq in the W-parametrisation: Bq - part must lie in span(W) + span(deltas)
vec = 0
for (i, j), v in Bq.items():
    if v: vec |= 1 << S['ei'](i, j)
print("  (direct membership test skipped; run solvers)")
st, model = solve(S, timeout=1800)
print("CMS result for the QR48 control:", st)
# ---- completeness check: QR48's own B satisfies all constraints of the model ----
K = 12; E = S['E']; ei = S['ei']
# diagonal: B(b_k,b_k) = |b_k|/2 + B(b_k, 1)  (basis[0] = all-ones)
diag_ok = all(Bq[(k, k)] == ((pc(basis[k]) // 2) + Bq[(0, k)]) % 2 for k in range(1, K))
# invariance: B(bb b_i, bb b_j) = B(b_i, b_j)
from v4sat import applym
coef = S['coef']
def Bval(x, y):
    cx = coef[x]; cy = coef[y]; s = 0
    for i in range(K):
        if not (cx >> i) & 1: continue
        for j in range(K):
            if (cy >> j) & 1: s ^= Bq[(min(i, j), max(i, j))]
    return s
inv_ok = all(Bval(applym(bb, basis[i], 24), applym(bb, basis[j], 24)) == Bq[(i, j)] for (i, j) in E)
# membership: Bq - part in span(W) + span(deltas)
def red(v, piv):
    for c in sorted(piv, reverse=True):
        if (v >> c) & 1: v ^= piv[c]
    return v
piv = {}
for w_ in S['W']:
    r = red(w_, piv)
    if r: piv[r.bit_length() - 1] = r
# deltas
orbs = []; seen = set()
for p in range(24):
    if p in seen: continue
    orbs.append((1 << p) | (1 << bb[p])); seen |= {p, bb[p]}
for R in orbs:
    d = 0
    for (i, j) in E:
        if pc(basis[i] & basis[j] & R) & 1: d |= 1 << ei(i, j)
    r = red(d, piv)
    if r: piv[r.bit_length() - 1] = r
mem_ok = red(vec ^ S['part'], piv) == 0
# good classes for every low word (min weight formula over the actual code)
mins = min(pc(w) for w in Wl if w)
print(f"QR48 own B: diagonal ok {diag_ok}, bb-invariant {inv_ok}, in valid affine space (mod swaps) {mem_ok}; d(QR48) = {mins}")
