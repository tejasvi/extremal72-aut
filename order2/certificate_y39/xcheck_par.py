"""Cross-check: rebuild mkpar's coordinates (same algorithm), evaluate the data-file function at random x and compare
with an independent count (lowcount.LowCounter) of X8b + X12 (kind x12b) on the same Gram matrix."""
import sys, random
import numpy as np
sys.path.insert(0, '<HOME>/c72/c2opt/math')
from mc import load_codes, pc, reduce_basis
from lowcount import LowCounter, basis_with_ones
which, fn = sys.argv[1], sys.argv[2]
gens, n2, d = load_codes()[int(which)], 36, 16
basis = basis_with_ones(gens, n2); k = len(basis)
def elem(i, j):
    D = np.zeros((k, k), dtype=np.int64)
    if i == j == 0: D[0, 0] = 1
    else:
        D[i, j] = D[j, i] = 1
        if i == 0 and j >= 1: D[j, j] ^= 1
    return D
elems = [(0, 0)] + [(i, j) for i in range(k) for j in range(i + 1, k)]
def gauge(p):
    return np.array([[(basis[i] >> p) & (basis[j] >> p) & 1 for j in range(k)] for i in range(k)], dtype=np.int64)
def vec(D): return [int(D[0, 0])] + [int(D[i, j]) for i in range(k) for j in range(i + 1, k)]
def tomask(vv):
    m = 0
    for t, b in enumerate(vv):
        if b: m |= 1 << t
    return m
cur = dict(reduce_basis([tomask(vec(gauge(p))) for p in range(n2)]))
dirs = []
for (i, j) in elems:
    m = tomask(vec(elem(i, j))); v = m
    for b in sorted(cur, reverse=True):
        if (v >> b) & 1: v ^= cur[b]
    if v:
        cur = reduce_basis(list(cur.values()) + [m]); dirs.append(elem(i, j))
B0 = np.zeros((k, k), dtype=np.int64)
for i in range(1, k): B0[i, i] = (pc(basis[i]) // 2) % 2
lines = open(fn).read().split('\n')
N, W, exp = map(int, lines[0].split())
assert N == len(dirs)
tabs = []
for w in range(W):
    r, h = lines[1 + w].split(); tabs.append(int(h, 16))
s0 = list(map(int, lines[1 + W].split()))
E = [list(map(int, lines[2 + W + v].split())) for v in range(N)]
LC = LowCounter(gens, n2, d)
assert LC.basis == basis
rng = random.Random(3)
agree = 0; tot = 0; vals = []
for _ in range(60):
    xs = [v for v in range(N) if rng.getrandbits(1)]
    M = B0.copy(); syn = s0[:]
    for v in xs:
        M = (M + dirs[v]) % 2; syn = [a ^ b for a, b in zip(syn, E[v])]
    assert LC.check_gram(M)
    g = sum((tabs[w] >> syn[w]) & 1 for w in range(W)) % 2
    c = LC.counts(M)
    ind = (c.get((8, 2), 0) + c.get((12, 0), 0)) % 2
    agree += (g == ind); tot += 1; vals.append(g)
print(f"code {which}: data-file g vs independent X8b+X12 parity: agree {agree}/{tot}; g values {sorted(set(vals))}")
