"""Partial-syndrome potential of an LTS key.  For a package (instance with .meta, flag, Aut(Y) perms) and key word k0:
(1) check the checkability criterion against the instance levels: B(y,c) (c disjoint from y) is determined at level t
    iff min(L(y), L(c), L(y+c)) <= t, L(x) = index of the top flag vector in x; so a constraint word y is checkable at
    t iff y in W_t or every c in Y_y has min(L(c), L(y+c)) <= t;
(2) for every g in G and level t: d_g(t) = dim of the determined part of the transported k0-syndrome,
    {c in Y_k0 : min(L(g k0), L(g c), L(g k0 + g c)) <= t} (a subspace of Y_k0).
Usage: partbits.py CI PKGDIR K0 [LEVELS]"""
import sys, os, pickle, itertools
import numpy as np
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
from instio import read_inst
from keycheck import closure_size


def closure(perms):
    idp = tuple(range(36)); seen = {idp}; fr = [idp]
    while fr:
        nf = []
        for p in fr:
            for g in perms:
                q = tuple(g[p[i]] for i in range(36))
                if q not in seen: seen.add(q); nf.append(q)
        fr = nf
    return sorted(seen)


def ap(p, y):
    z = 0
    while y:
        b = y & -y; i = b.bit_length() - 1; z |= 1 << p[i]; y ^= b
    return z


ci = int(sys.argv[1]); pk = sys.argv[2]; k0 = int(sys.argv[3])
levels = [int(x) for x in sys.argv[4].split(',')] if len(sys.argv) > 4 else list(range(3, 10))
flag = [int(x) for x in open(f'{pk}/flag.txt').read().split()[1:]]
I = read_inst(f'{pk}/inst.txt'); cons = I['cons']
perms = pickle.load(open(os.path.join(here, '..', 'inst', 'invs.pkl'), 'rb'))[ci]['perms']
G = closure(perms)
# all words of Y with their top flag index
n = len(flag); words = np.zeros(1 << n, dtype=np.int64); L = np.full(1 << n, -1, dtype=np.int64)
for i, v in enumerate(flag):
    words[1 << i: 1 << (i + 1)] = words[0: 1 << i] ^ v; L[1 << i: 1 << (i + 1)] = i
Lw = dict(zip(words.tolist(), L.tolist()))
def Yd(y):          # words of Y disjoint from y
    return words[(words & y) == 0]
def lev_fun(y, c):
    return min(Lw[y], Lw[c], Lw[y ^ c])
# (1) criterion vs instance levels
bad = 0; tot = 0
for c in cons[:: max(1, len(cons) // 400)]:
    y = c['y']; ys = Yd(y)
    pred = Lw[y] if False else None
    m = max(min(Lw[int(x)], Lw[int(x) ^ y]) for x in ys)
    pred = min(Lw[y], m)
    tot += 1; bad += (pred != c['lv'])
    if pred != c['lv'] and bad <= 5: print(f"  mismatch y={y} wt={c['wt']} inst lv={c['lv']} pred={pred} L(y)={Lw[y]}")
print(f"criterion check: {tot - bad}/{tot} sampled constraints match the instance level")
# (2) d_g(t) for the key word
yk = Yd(k0); m0 = int(np.log2(len(yk)))
print(f"Y{ci} |G|={len(G)} k0={k0} L(k0)={Lw[k0]} |Y_k0|=2^{m0}")
rows = []
for g in G:
    u = ap(g, k0); Lu = Lw[u]
    gl = [min(Lw[ap(g, int(c))], Lw[u ^ ap(g, int(c))]) for c in yk]
    rows.append((Lu, gl))
for t in levels:
    hist = {}
    for Lu, gl in rows:
        if Lu <= t: d = m0
        else:
            cnt = sum(1 for x in gl if x <= t); d = int(round(np.log2(cnt))) if cnt else 0
        hist[d] = hist.get(d, 0) + 1
    full = hist.get(m0, 0)
    print(f"  t={t:2d} full={full:4d} partial " + ' '.join(f"d{d}:{hist[d]}" for d in sorted(hist) if d != m0))
