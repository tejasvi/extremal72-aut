"""Positive control, part 1: QR48 (extended binary QR code, p = 47), the fixed-point-free order-3 automorphism
sigma: x -> -1/(x+1) on P^1(F_47) (coordinate i <-> i in F_47 for i < 47, coordinate 47 <-> infinity), the
contracted fixed code D (binary [16,8]) and the F4-linear code E (16 coordinates) of words with even weight on
every cycle (cycle bits b0 b1 b2 along x, sigma x, sigma^2 x -> (b0+b2) + (b1+b2) w).
Writes ctl48/qr48_DE.txt: D generator rows (16-bit ints) and E generator rows (pairs of 16-bit planes a,b)."""
import sys, itertools
from flint import nmod_poly
p = 47; n = 48
fl = nmod_poly([1] + [0] * (p - 1) + [1], 2).factor()[1]          # x^47 + 1
degs = sorted(f.degree() for f, e in fl)
assert degs == [1, 23, 23], degs
facs = [f for f, e in fl if f.degree() == 23]
def code_from(g):
    gm = sum(1 << i for i, c in enumerate(g.coeffs()) if int(c) % 2)
    rows = []
    for s in range(24):
        r = gm << s
        r |= (bin(r).count('1') & 1) << p
        rows.append(r)
    return rows
def span(rows):
    S = [0]
    for r in rows: S += [s ^ r for s in S]
    return S
inv = {x: pow(x, p - 2, p) for x in range(1, p)}
INF = 47
def sig(x):
    if x == INF: return 0                       # -1/(inf+1) = 0
    if x == p - 1: return INF                   # x+1 = 0
    return (-inv[(x + 1) % p]) % p
perm = [sig(x) for x in range(n)]
assert all(perm[perm[perm[x]]] == x for x in range(n)) and all(perm[x] != x for x in range(n))
def apply(perm, w):
    o = 0
    for i in range(n):
        if (w >> i) & 1: o |= 1 << perm[i]
    return o
chosen = None
for g in facs:
    rows = code_from(g)
    W = span(rows); Ws = set(W)
    wd = {}
    for w in W: wd[bin(w).count('1')] = wd.get(bin(w).count('1'), 0) + 1
    ok = all(apply(perm, r) in Ws for r in rows)
    print("factor:", "weight distribution", sorted(wd.items()), "sigma automorphism:", ok)
    if ok and min(k for k in wd if k > 0) == 12: chosen = (rows, Ws, W)
assert chosen is not None
rows, Ws, W = chosen
# cycles
seen = set(); cycles = []
for x in range(n):
    if x not in seen:
        c = [x, perm[x], perm[perm[x]]]; seen.update(c); cycles.append(c)
assert len(cycles) == 16
# fixed subcode -> D
Dset = set()
for w in W:
    if apply(perm, w) == w:
        d = 0
        for i, c in enumerate(cycles):
            if (w >> c[0]) & 1: d |= 1 << i
        Dset.add(d)
print("|D| =", len(Dset), "weights", sorted({bin(d).count('1') for d in Dset}))
# E: words with even weight on every cycle
def f4val(b0, b1, b2):
    a = b0 ^ b2; bb = b1 ^ b2
    return a | (bb << 1)
Eset = set()
for w in W:
    vals = []
    ok = True
    for c in cycles:
        b = [(w >> c[j]) & 1 for j in range(3)]
        if sum(b) % 2: ok = False; break
        vals.append(f4val(*b))
    if ok:
        a = sum(((v & 1) << i) for i, v in enumerate(vals)); bb = sum((((v >> 1) & 1) << i) for i, v in enumerate(vals))
        Eset.add((a, bb))
print("|E| =", len(Eset), "(4^8 =", 4 ** 8, ")")
wE = {}
for a, b in Eset: k = bin(a | b).count('1'); wE[k] = wE.get(k, 0) + 1
print("E weight distribution", sorted(wE.items()))
# bases
def f2basis(vs):
    B = []
    for v in sorted(vs, reverse=True):
        x = v
        for b in B: x = min(x, x ^ b)
        if x: B.append(x)
    return B
DB = f2basis(Dset)
assert len(DB) == 8
# F4 basis of E: greedy over F2 span of (a,b) as 32-bit
def pack(a, b): return a | (b << 16)
EB2 = f2basis([pack(a, b) for a, b in Eset])
assert len(EB2) == 16
# pick F4 basis: elements independent over F4 -> take vectors v not in F4-span of chosen
def mulw(a, b): return (b, a ^ b)
chosenE = []; spanset = {(0, 0)}
for a, b in sorted(Eset):
    if (a, b) in spanset: continue
    chosenE.append((a, b))
    new = set()
    for (x, y) in spanset:
        for lam in range(1, 4):
            ua, ub = (a, b) if lam == 1 else (mulw(a, b) if lam == 2 else mulw(*mulw(a, b)))
            new.add((x ^ ua, y ^ ub))
    spanset |= new
    if len(chosenE) == 8: break
assert len(spanset) == 4 ** 8
with open('qr48_DE.txt', 'w') as f:
    f.write(' '.join('%04x' % d for d in DB) + '\n')
    f.write(''.join('%08x%08x' % (a, b) for a, b in chosenE) + '\n')
print("D basis", ['%04x' % d for d in DB])
print("wrote ctl48/qr48_DE.txt")
