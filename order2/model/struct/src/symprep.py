"""Symmetry file for the lex-leader-on-transported-syndromes (LTS) test of lwe3.c.
G = Aut(Y) (closure of generator permutations of the m coordinates), w0 = first flag vector, O = G-orbit of w0.
Syndromes s_y = B(y,.) on Y_y in the instance's basis ub_y (from INSTANCE.meta) are gauge-invariant.
(B^g)(x,y) = B(gx,gy) => s_{w0}(B^g) = t_u(s_u(B)) with u = g w0, (t_u s)_j = parity(coords_u(g ub0_j) & s).
canon[s] = min over h in Stab(w0) of s o h.  Test (complete for lex-least orbit members): s0 canonical and
s0 <= canon[t_u(s_u)] for every u in O whose syndrome is determined.
Output SYMFILE: 'm c0 nent' / canon table (2^m ints) / per u != w0: 'c_u row_0 .. row_{m-1}'.
Usage (code): symprep.py CI INSTANCE SYMFILE    (generic use via import: prep(Ygens, gens, m, instance, out))"""
import sys, os, pickle
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

def closure(gens, m):
    idp = tuple(range(m)); seen = {idp}; fr = [idp]
    while fr:
        nf = []
        for p in fr:
            for g in gens:
                q = tuple(g[p[i]] for i in range(m))
                if q not in seen: seen.add(q); nf.append(q)
        fr = nf
    return list(seen)

def ap(perm, w, m):
    o = 0
    for i in range(m):
        if (w >> i) & 1: o |= 1 << perm[i]
    return o

def coords_fn(basis):
    piv = {}
    for k, b in enumerate(basis):
        v = b; tr = 1 << k
        for c in sorted(piv, reverse=True):
            if (v >> c) & 1: v ^= piv[c][0]; tr ^= piv[c][1]
        assert v
        piv[v.bit_length() - 1] = (v, tr)
    def coords(x):
        tr = 0
        for c in sorted(piv, reverse=True):
            if (x >> c) & 1: x ^= piv[c][0]; tr ^= piv[c][1]
        assert x == 0, "vector not in span"
        return tr
    return coords

def prep(gens, m, instance, out, w0, verbose=True):
    meta = [list(map(int, l.split())) for l in open(instance + '.meta')]
    idx = {row[0]: k for k, row in enumerate(meta)}
    G = closure(gens, m)
    O = {}
    for g in G:
        u = ap(g, w0, m)
        if u not in O: O[u] = g
    St = [g for g in G if ap(g, w0, m) == w0]
    c0 = idx[w0]; ub0 = meta[c0][1:]; mm = len(ub0)
    co0 = coords_fn(ub0)
    # canonical table over all 2^mm syndromes
    acts = [[co0(ap(h, ub0[j], m)) for j in range(mm)] for h in St]
    canon = [-1] * (1 << mm)
    for s in range(1 << mm):
        if canon[s] >= 0: continue
        orb = set()
        for rows in acts:
            o = 0
            for j, r in enumerate(rows):
                if bin(r & s).count('1') & 1: o |= 1 << j
            orb.add(o)
        mn = min(orb)
        for x in orb: canon[x] = mn
    ents = []
    for u, g in O.items():
        if u == w0: continue
        cu = idx[u]; ubu = meta[cu][1:]; assert len(ubu) == mm
        cou = coords_fn(ubu)
        rows = [cou(ap(g, ub0[j], m)) for j in range(mm)]
        ents.append((cu, rows))
    with open(out, 'w') as f:
        f.write(f"{mm} {c0} {len(ents)}\n")
        f.write(' '.join(map(str, canon)) + '\n')
        for cu, rows in ents:
            f.write(' '.join(map(str, [cu] + rows)) + '\n')
    if verbose:
        ncl = len(set(canon))
        print(f"|G| = {len(G)}, |orbit(w0)| = {len(O)}, |Stab(w0)| = {len(St)}, syndrome dim {mm}, classes over all 2^m: {ncl}")
    return G, O, St

if __name__ == '__main__':
    ci = int(sys.argv[1]); inst = sys.argv[2]; out = sys.argv[3]
    codes = load()
    res = pickle.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'invs.pkl'), 'rb'))
    gens = res[ci]['perms']
    # w0 = first flag vector = the word of the level-0 constraint with the smallest weight... use the flag file
    flagf = sys.argv[4]
    w0 = int([l for l in open(flagf) if l.startswith('FLAG')][0].split()[1])
    prep(gens, 36, inst, out, w0)
