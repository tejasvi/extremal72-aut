"""LTS-r symmetry file for lwe7.c (lex-leader on the key K(B) = (s_w0(B), ..., s_w{r-1}(B)), w_i = first r flag
vectors, all low-weight words with constraints).  For every g in G = <gens> (closure; identity excluded) and every
i < r: the constraint index of g w_i and the transport matrix T_{g,i}: s_{w_i}(B^g) = T_{g,i} s_{g w_i}(B), rows
T_{g,i}[j] = coords_{g w_i}(g ub_i[j]) (ub = the instance's basis of Y_y from INSTANCE.meta).
Format: 'LTSR r nG' / 'c_0 m_0 ... c_{r-1} m_{r-1}' / nG lines 'c_{g w_0} rows.. c_{g w_1} rows.. ...'.
Usage: prep2(gens, m, instance, out, flag, r)  or  symprep2.py CI INSTANCE OUT FLAGFILE R"""
import sys, os, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *
from symprep import closure, coords_fn

def make_ap(m):
    def ap(perm, w):
        o = 0
        while w:
            b = w & -w; i = b.bit_length() - 1
            o |= 1 << perm[i]; w ^= b
        return o
    return ap

def prep2(gens, m, instance, out, flag, r, verbose=True, G=None):
    ap = make_ap(m)
    meta = [list(map(int, l.split())) for l in open(instance + '.meta')]
    idx = {row[0]: k for k, row in enumerate(meta)}
    key = flag[:r]
    for w in key: assert w in idx, "key word without constraint"
    if G is None: G = closure(gens, m)
    idt = tuple(range(m))
    cinfo = [(idx[w], len(meta[idx[w]]) - 1) for w in key]
    cache = {}
    def coords_of(c):
        if c not in cache: cache[c] = coords_fn(meta[c][1:])
        return cache[c]
    lines = []
    for g in G:
        if tuple(g) == idt: continue
        parts = []
        for i, w in enumerate(key):
            v = ap(g, w); c = idx[v]; co = coords_of(c)
            ub = meta[cinfo[i][0]][1:]
            rows = [co(ap(g, ub[j])) for j in range(len(ub))]
            parts.append(str(c)); parts += [str(x) for x in rows]
        lines.append(' '.join(parts))
    with open(out, 'w') as f:
        f.write(f"LTSR {r} {len(lines)}\n")
        f.write(' '.join(f"{c} {mm}" for c, mm in cinfo) + '\n')
        f.write('\n'.join(lines) + '\n')
    if verbose: print(f"LTSR file: r = {r}, |G| = {len(G)}, key constraints {cinfo}")
    return G

if __name__ == '__main__':
    ci = int(sys.argv[1]); inst = sys.argv[2]; out = sys.argv[3]; flagf = sys.argv[4]; r = int(sys.argv[5])
    res = pickle.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'invs.pkl'), 'rb'))
    flag = [int(x) for x in [l for l in open(flagf) if l.startswith('FLAG')][0].split()[1:]]
    prep2(res[ci]['perms'], 36, inst, out, flag, r)
