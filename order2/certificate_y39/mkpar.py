"""Export data for the C parity checker (csrc/parcheck.c).
Certificate function g(B) = sum_{y in support} G_y(s_y(B)) mod 2, G_y given as a bit table over the syndrome space
(basis of Y_y modulo 1+y).  Coordinates: B = B0 + sum_v x_v E_v, E_v (v < N) a basis of the B-direction space modulo
the gauge (built greedily from elementary Gram directions).  Output file format (text):
  N W d expected
  then W lines: r tablehex   (r = syndrome bits of the word, table = 2^r bits as hex string, bit s = G_y(s))
  then base syndromes: W ints;  then N lines of W ints (direction syndromes).
usage: mkpar.py CODE|golay|qr48 CERTKIND OUT   CERTKIND: x12b (Y39 cert: a2-parity on w8 + [s=0] on w12),
       x8 (Golay: [s=0] on octads), all (sum of all bad patterns = (A8+A12)/2)"""
import sys
import numpy as np
from itertools import combinations
sys.path.insert(0, '<HOME>/c72/c2opt/math')
from mc import span_np, pc, reduce_basis, load_codes, qr_pairmodel
from lowcount import basis_with_ones
from golay import golay24

which, kind, out = sys.argv[1], sys.argv[2], sys.argv[3]
if which == 'golay':
    gens, n2, d = golay24(), 24, 12
elif which == 'qr48':
    gens, n2, d = qr_pairmodel(47)['Ygens'], 24, 12
else:
    gens, n2, d = load_codes()[int(which)], 36, 16
basis = basis_with_ones(gens, n2)
k = len(basis)
piv = {}
for i, g in enumerate(basis):
    v, c = g, 1 << i
    for b in sorted(piv, reverse=True):
        if (v >> b) & 1:
            v ^= piv[b][0]; c ^= piv[b][1]
    piv[v.bit_length() - 1] = (v, c)
pivs = sorted(piv.items(), reverse=True)
def coords(w):
    c = 0
    for b, (v, cc) in pivs:
        if (w >> b) & 1:
            w ^= v; c ^= cc
    assert w == 0
    return c
Y = span_np(basis)
wy = np.bitwise_count(Y)
full = (1 << n2) - 1

def word_data(y):
    """syndrome basis (Y_y modulo 1+y) and small-pattern syndrome lists by size"""
    j = pc(y)
    sh = [int(u) for u in Y[(Y & np.uint64(y)) == 0].tolist()]
    comp = full ^ y
    bas = []
    cur = [comp]
    for u in sh:
        if len(reduce_basis(cur + [u])) > len(reduce_basis(cur)):
            cur.append(u); bas.append(u)
    sizes = [s for s in range(0, (d - j + 1) // 2) if s % 2 == (j // 2) % 2]
    outside = [i for i in range(n2) if not (y >> i) & 1]
    mult = {}
    for s in sizes:
        for cmb in combinations(outside, s):
            e = 0
            for i in cmb: e |= 1 << i
            syn = 0
            for t, u in enumerate(bas):
                syn |= (pc(e & u) & 1) << t
            mult.setdefault(syn, []).append(s)
    return bas, mult

words = []
for j in range(2, d, 2):
    for y in Y[wy == j].tolist():
        y = int(y)
        if kind == 'x12b' and j not in (8, 12):
            continue
        if kind == 'x8' and j != 8:
            continue
        bas, mult = word_data(y)
        if not mult:
            continue
        r = len(bas)
        tab = 0
        for syn, ss in mult.items():
            if kind == 'x12b':
                v = (sum(1 for t in ss if t == 2) % 2) if j == 8 else 1
            elif kind == 'x8':
                v = 1 if 0 in ss else 0
            else:
                v = len(ss) % 2
            if v:
                tab |= 1 << syn
        if tab == 0:
            continue
        words.append((y, r, tab, coords(y), [coords(u) for u in bas]))
W = len(words)
# B-direction space: symmetric k x k Gram matrices with Delta_ii = Delta_i0 (i >= 1), Delta_00 free.
def elem(i, j):
    D = np.zeros((k, k), dtype=np.int64)
    if i == j == 0:
        D[0, 0] = 1
    else:
        D[i, j] = D[j, i] = 1
        if i == 0 and j >= 1:
            D[j, j] ^= 1          # Delta_jj = Delta_j0
    return D
elems = [(0, 0)] + [(i, j) for i in range(k) for j in range(i + 1, k)]
assert len(elems) == 1 + k * (k - 1) // 2
def gauge(p):
    D = np.zeros((k, k), dtype=np.int64)
    for i in range(k):
        for j in range(k):
            D[i, j] = (basis[i] >> p) & (basis[j] >> p) & 1
    return D
def vec(D):
    """coordinates of a direction in the elementary basis (off-diagonal + D00)"""
    return [int(D[0, 0])] + [int(D[i, j]) for i in range(k) for j in range(i + 1, k)]
def tomask(vv):
    m = 0
    for t, b in enumerate(vv):
        if b: m |= 1 << t
    return m
# check gauge directions satisfy the diagonal condition
for p in range(n2):
    G = gauge(p)
    for i in range(1, k):
        assert G[i, i] == G[i, 0]
gm = [tomask(vec(gauge(p))) for p in range(n2)]
gp = reduce_basis(gm)
ng = len(gp)
dirs = []
cur = dict(gp)
for (i, j) in elems:
    m = tomask(vec(elem(i, j)))
    v = m
    for b in sorted(cur, reverse=True):
        if (v >> b) & 1: v ^= cur[b]
    if v:
        cur = reduce_basis(list(cur.values()) + [m])
        dirs.append(elem(i, j))
N = len(dirs)
print(f"{which}: k={k}, gauge rank {ng}, direction space {len(elems)}, quotient N = {N}, words W = {W}", flush=True)
B0 = np.zeros((k, k), dtype=np.int64)
for i in range(1, k):
    B0[i, i] = (pc(basis[i]) // 2) % 2          # B(g_i,g_i) = |g_i|/2 + B(g_i, 1) with B(g_i,1) = B0[i,0] = 0
CY = np.array([[(w[3] >> i) & 1 for i in range(k)] for w in words], dtype=np.int64)
rmax = max(w[1] for w in words)
UB = np.zeros((W, rmax, k), dtype=np.int64)
for wi, w in enumerate(words):
    for t, c in enumerate(w[4]):
        UB[wi, t] = [(c >> i) & 1 for i in range(k)]
pw = (1 << np.arange(rmax)).astype(np.int64)
def synd(M):
    R = (CY @ M) % 2
    return (np.einsum('wk,wtk->wt', R, UB) % 2) @ pw
s0 = synd(B0)
E = [synd((B0 + D) % 2) ^ s0 for D in dirs]
# affine-linearity sanity
rng = np.random.default_rng(5)
for _ in range(20):
    xs = [v for v in range(N) if rng.integers(2)]
    M = B0.copy()
    s = s0.copy()
    for v in xs:
        M = (M + dirs[v]) % 2; s ^= E[v]
    assert np.array_equal(s, synd(M))
# diagonal-condition sanity: s_y(1+y) parity is automatic: check B(y, 1+y) = |y|/2 for random forms
for _ in range(5):
    M = B0.copy()
    for v in range(N):
        if rng.integers(2): M = (M + dirs[v]) % 2
    for w in words[:30]:
        y = w[0]
        a = np.array([(coords(y) >> i) & 1 for i in range(k)]); b = np.array([(coords(full ^ y) >> i) & 1 for i in range(k)])
        assert (a @ M @ b) % 2 == (pc(y) // 2) % 2
expected = int(sys.argv[4]) if len(sys.argv) > 4 else 1
dmax = max(int(sys.argv[5]) if len(sys.argv) > 5 else 0, 0)
with open(out, 'w') as f:
    f.write(f"{N} {W} {expected}\n")
    for (y, r, tab, cy, cu) in words:
        f.write(f"{r} {tab:x}\n")
    f.write(' '.join(str(int(v)) for v in s0) + '\n')
    for e in E:
        f.write(' '.join(str(int(v)) for v in e) + '\n')
print('written', out)
