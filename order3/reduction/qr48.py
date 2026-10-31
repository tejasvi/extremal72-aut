"""Positive control: QR48 (extended binary QR code, p=47) and its fixed-point-free automorphism of order 3
x -> -1/(x+1) on PG(1,47).  Decompose C = F (+) E: F = tripled [16,8] doubly-even code G16, E = Hermitian
self-dual [16,8] code over F4.  Check the length-48 analogue of the support conditions and the weight formula."""
import sys, pickle, itertools, collections
import os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from f4lib import *
p = 47; INF = 47; n = 48
Q = sorted({(x * x) % p for x in range(1, p)})
assert len(Q) == 23
def cyc(v, s): return ((v << s) | (v >> (p - s))) & ((1 << p) - 1)
best = None
for base in (sum(1 << r for r in Q), 1 | sum(1 << r for r in Q)):
    gens = [cyc(base, s) for s in range(p)]
    r = bin_rank(gens)
    # extend by overall parity at position 47
    ext = [g | ((pc(g) & 1) << INF) for g in bin_basis(gens)]
    print("base has", pc(base), "ones; cyclic rank", r)
    if r == 24: best = ext
# QR code of dim 24 (contains the all-ones word of length 47 after extension?)
C = best
assert bin_rank(C) == 24
# self-dual check
assert all(pc(a & b) % 2 == 0 for a in C for b in C), "not self-orthogonal"
# doubly even + min weight (2^24 words; use Gray code)
def weight_dist(basis):
    k = len(basis); cnt = collections.Counter(); x = 0
    cnt[0] += 1
    for i in range(1, 1 << k):
        j = (i & -i).bit_length() - 1; x ^= basis[j]; cnt[pc(x)] += 1
    return dict(sorted(cnt.items()))
WD = weight_dist(C); print("QR48 weight distribution:", WD)
assert min(w for w in WD if w) == 12 and all(w % 4 == 0 for w in WD)
# automorphism sigma: x -> -1/(x+1) on {0..46, INF}
def sig(x):
    if x == INF: return 0                 # -1/(inf+1) = 0
    if x == p - 1: return INF             # -1/0 = inf
    return (-pow(x + 1, p - 2, p)) % p
perm = [sig(x) for x in range(n)]
assert all(perm[perm[perm[x]]] == x for x in range(n)) and all(perm[x] != x for x in range(n))
def apply(perm, v):
    o = 0
    for i in range(n):
        if v >> i & 1: o |= 1 << perm[i]
    return o
Cset_basis = C
# membership test via rank
def in_code(v): return bin_rank(C + [v]) == 24
assert all(in_code(apply(perm, g)) for g in C), "sigma not an automorphism"
print("sigma is a fixed-point-free automorphism of order 3")
# cycles
seen = set(); cycles = []
for x in range(n):
    if x in seen: continue
    c = (x, perm[x], perm[perm[x]]); cycles.append(c); seen |= set(c)
assert len(cycles) == 16
# fixed subcode: words constant on cycles; E-part: words even on every cycle
allw = bin_span(C)   # 2^24 words; fine
fixed = [w for w in allw if all(((w >> a) & 1) == ((w >> b) & 1) == ((w >> c) & 1) for a, b, c in cycles)]
print("fixed subcode size", len(fixed))
G16 = sorted({sum(((w >> c[0]) & 1) << i for i, c in enumerate(cycles)) for w in fixed})
print("G16 weight dist", collections.Counter(pc(g) for g in G16))
evenw = [w for w in allw if all(((w >> a) ^ (w >> b) ^ (w >> c)) & 1 == 0 for a, b, c in cycles)]
print("even-on-cycles subcode size", len(evenw), "= 4^8?", len(evenw) == 4 ** 8)
# map to F4: pattern (u0,u1,u2) on (p0,p1,p2): 011->1, 101->w, 110->wbar
code = {(0, 1, 1): (1, 0), (1, 0, 1): (0, 1), (1, 1, 0): (1, 1), (0, 0, 0): (0, 0)}
def to_f4(w):
    lo = hi = 0
    for i, (a, b, c) in enumerate(cycles):
        l, h = code[((w >> a) & 1, (w >> b) & 1, (w >> c) & 1)]
        lo |= l << i; hi |= h << i
    return (lo, hi)
E = sorted({to_f4(w) for w in evenw})
assert len(E) == 4 ** 8
Eset = set(E)
# F4-linearity (sigma <-> multiplication by w) and Hermitian self-duality
assert all(mulw(e) in Eset for e in E)
basisE = rref(E, 16); assert len(basisE) == 8
assert all(herm(a, b) == 0 for a in basisE for b in basisE)
wdE = collections.Counter(wt(e) for e in E); print("E16 weight distribution:", dict(sorted(wdE.items())))
# length-48 conditions
tet = [g for g in G16 if pc(g) == 4]; oc8 = set(g for g in G16 if pc(g) == 8)
bad6 = sum(1 for e in E if wt(e) == 6 and any((t & supp(e)) == t for t in tet))
bad8 = sum(1 for e in E if wt(e) == 8 and supp(e) in oc8)
print("weight-6 words whose support contains a tetrad:", bad6, "; weight-8 words with support a weight-8 word of G16:", bad8)
# weight formula check: wt(f+e) = 3|g| + 2 wt(e) - 4|g & supp e|
import random
rnd = random.Random(5)
def from_parts(g, e):
    w = 0
    inv = {v: k for k, v in code.items()}
    for i, (a, b, c) in enumerate(cycles):
        u = inv[(((e[0] >> i) & 1), ((e[1] >> i) & 1))]
        bits = [u[0], u[1], u[2]]
        if (g >> i) & 1: bits = [1 - x for x in bits]
        w |= (bits[0] << a) | (bits[1] << b) | (bits[2] << c)
    return w
for _ in range(2000):
    g = rnd.choice(G16); e = rnd.choice(E); w = from_parts(g, e)
    assert in_code(w) if _ < 50 else True
    assert pc(w) == 3 * pc(g) + 2 * wt(e) - 4 * pc(g & supp(e))
print("weight formula verified on 2000 random pairs")
# G16 identification: e8+e8 or d16+ (count weight-4 words: e8+e8 has 28, d16+ has 28 too; use structure)
print("G16 weight-4 words:", len(tet))
# is G16 decomposable (two disjoint 8-sets each supporting [8,4,4])?
supports = [g for g in G16 if pc(g) == 8]
dec = [s for s in supports if all(pc(s & t) in (0, 4) for t in tet) and sum(1 for t in tet if (t & s) == t) == 14]
print("weight-8 words of G16 that are e8 components:", len(dec))
pickle.dump(dict(cycles=cycles, G16=G16, E=basisE, perm=perm, C=C), open(os.path.join(HERE, 'qr48.pkl'), 'wb'))
