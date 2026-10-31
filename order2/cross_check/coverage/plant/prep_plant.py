"""Prepare data for plant.c (audit, independent code). usage: prep_plant.py PKGDIR CI OUT
Reads PKGDIR/inst.txt.meta (word, syndrome basis per constraint, instance order), inst.txt.pkl (flag w, Gram-entry
forms entf over the free variables), the group generators of code CI (explore frozen invs.pkl; each generator is
checked to preserve Y), closes the group (BFS), and writes: 'N NG NC', the 18x36 coordinate matrix R (R w_k = e_k),
171 Gram-entry forms (E order), NG permutations, NC constraints 'y m ub...'."""
import sys, pickle
pkg, ci, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
FROZ = '<HOME>/c72/explore/runs2/frozen/'
inv = pickle.load(open(FROZ + 'invs.pkl', 'rb'))[ci]
codes = []
for b in open(FROZ + 'codes36.txt').read().strip().split('\n\n'):
    rows = [l.strip() for l in b.strip().split('\n') if l.strip()]
    codes.append([sum(int(ch) << j for j, ch in enumerate(r)) for r in rows])
Ygen = codes[ci]
assert Ygen == inv['code'], 'invs.pkl code differs from codes36'
def red(basis, v):
    for b in basis:
        v = min(v, v ^ b)
    return v
Yb = []
for g in Ygen:
    r = red(Yb, g)
    if r: Yb.append(r)
assert len(Yb) == 18
def inY(x): return red(Yb, x) == 0
def ap(p, x):   # bit i -> bit p[i]
    o = 0
    for i in range(36):
        if (x >> i) & 1: o |= 1 << p[i]
    return o
gens = [tuple(p) for p in inv['perms']]
for p in gens:
    assert sorted(p) == list(range(36))
    for g in Ygen: assert inY(ap(p, g)), 'generator does not preserve Y'
# closure
idp = tuple(range(36)); G = [idp]; seen = {idp}
k = 0
while k < len(G):
    x = G[k]; k += 1
    for s in gens:
        y = tuple(s[x[i]] for i in range(36))
        if y not in seen: seen.add(y); G.append(y)
pk = pickle.load(open(pkg + '/inst.txt.pkl', 'rb'))
w, entf, E, N = pk['w'], pk['entf'], pk['E'], pk['N']
assert len(w) == 18 and len(E) == 171
for x in w: assert inY(x)
# R: 18x36 with R w_k = e_k (extend w by unit vectors to a basis of F2^36, invert)
cols = list(w); B = list(w)
basis = []
for x in cols:
    basis.append(x)
for i in range(36):
    if red([], 0) == 0: pass
ext = list(w); rb = []
def addvec(rb, v):
    for b in rb: v = min(v, v ^ b)
    if v: rb.append(v); return True
    return False
for x in w: assert addvec(rb, x)
for i in range(36):
    if len(ext) == 36: break
    if addvec(rb, 1 << i): ext.append(1 << i)
assert len(ext) == 36
# matrix A with columns ext: solve for each unit vector e_a its coordinates in basis ext -> column a of A^{-1}
# use elimination with tracking
rows = [(ext[k], 1 << k) for k in range(36)]   # vector, combination of basis indices
piv = {}
for v, c in rows:
    for bit in sorted(piv, reverse=True):
        if (v >> bit) & 1: v ^= piv[bit][0]; c ^= piv[bit][1]
    assert v
    piv[v.bit_length() - 1] = (v, c)
def coords_ext(x):
    c = 0
    for bit in sorted(piv, reverse=True):
        if (x >> bit) & 1: x ^= piv[bit][0]; c ^= piv[bit][1]
    assert x == 0
    return c
R = [0] * 18
for a in range(36):
    c = coords_ext(1 << a)
    for k in range(18):
        if (c >> k) & 1: R[k] |= 1 << a
for k in range(18):
    for kk in range(18):
        assert (bin(R[kk] & w[k]).count('1') & 1) == (1 if k == kk else 0)
meta = [list(map(int, l.split())) for l in open(pkg + '/inst.txt.meta')]
with open(out, 'w') as f:
    f.write(f'{N} {len(G)} {len(meta)}\n')
    f.write(' '.join(map(str, R)) + '\n')
    for (i, j), (vm, c) in zip(E, entf): f.write(f'{i} {j} {vm:x} {c}\n')
    for g in G: f.write(' '.join(map(str, g)) + '\n')
    for row in meta: f.write(f'{row[0]} {len(row)-1} ' + ' '.join(map(str, row[1:])) + '\n')
print(f'N {N} |G| {len(G)} constraints {len(meta)}; generators preserve Y; R verified')
# odd-order elements (for B0 with nontrivial stabiliser): indices into G, order > 1 and odd
def order(p):
    cur = p; k = 1
    while cur != idp:
        cur = tuple(p[cur[i]] for i in range(36)); k += 1
        if k > 100000: return 0
    return k
odd = [k for k, g in enumerate(G) if g != idp and order(g) % 2 == 1]
with open(out + '.odd', 'w') as f:
    f.write(' '.join(map(str, odd)) + '\n')
print(f'odd-order elements: {len(odd)}')
