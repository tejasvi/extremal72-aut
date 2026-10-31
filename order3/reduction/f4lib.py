"""Small F4 / binary code helpers (pure python ints, bit-sliced F4 vectors).
F4 element a + b*w stored as (lo, hi) bits; vector = (lo_mask, hi_mask).  w^2 = w + 1.
Binary image per 3-cycle (p0, p1=sigma(p0), p2=sigma(p1)):  1 <-> 011, w <-> 101, wbar <-> 110
(so sigma acts as multiplication by w on E)."""
import itertools, random
pc = lambda x: bin(x).count('1')

def mulw(v):          # multiply vector by w
    lo, hi = v; return (hi, lo ^ hi)
def scal(lam, v):     # lam in 0..3 = (lo + 2 hi): 0, 1, w (=2), wbar (=3)
    if lam == 0: return (0, 0)
    if lam == 1: return v
    if lam == 2: return mulw(v)
    return mulw(mulw(v))
def add(u, v): return (u[0] ^ v[0], u[1] ^ v[1])
def supp(v): return v[0] | v[1]
def wt(v): return pc(v[0] | v[1])
def conj(v): lo, hi = v; return (lo ^ hi, hi)
def herm(u, v):       # sum u_i conj(v_i) -> element code 0..3
    cl, ch = conj(v); ul, uh = u
    p0 = (ul & cl) ^ (uh & ch); p1 = (ul & ch) ^ (uh & cl) ^ (uh & ch)
    return (pc(p0) & 1) | ((pc(p1) & 1) << 1)

def span(gens):
    """all codewords (as list of (lo,hi)) of the F4-span of gens"""
    words = [(0, 0)]
    for g in gens:
        g1 = g; g2 = mulw(g); g3 = mulw(g2)
        words = words + [add(w, g1) for w in words] + [add(w, g2) for w in words] + [add(w, g3) for w in words]
    return words

def rref(gens, n):
    """row-reduce F4 vectors; returns independent basis (list)"""
    rows = list(gens); basis = []
    # element-wise representation for elimination
    def get(v, i): return ((v[0] >> i) & 1) | (((v[1] >> i) & 1) << 1)
    inv = {1: 1, 2: 3, 3: 2}
    piv = []
    for v in rows:
        for (b, p) in zip(basis, piv):
            c = get(v, p)
            if c: v = add(v, scal(c, b))
        if v != (0, 0):
            p = next(i for i in range(n) if get(v, i)); c = get(v, p)
            v = scal(inv[c], v)
            # reduce existing basis at new pivot
            nb = []
            for b in basis:
                cb = get(b, p)
                nb.append(add(b, scal(cb, v)) if cb else b)
            basis = nb + [v]; piv.append(p)
    return basis

def bin_rank(vecs):
    basis = {}
    r = 0
    for v in vecs:
        x = v
        while x:
            h = x.bit_length() - 1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; r += 1; break
    return r

def bin_span(gens):
    words = [0]
    for g in gens:
        words = words + [w ^ g for w in words]
    return words

def bin_basis(vecs):
    basis = {}
    for v in vecs:
        x = v
        while x:
            h = x.bit_length() - 1
            if h in basis: x ^= basis[h]
            else: basis[h] = x; break
    return list(basis.values())
