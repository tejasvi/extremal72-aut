"""Hybrid LTS-r data for lwe8.c.  Key K(B) = (s_w0(B), ..., s_w{r-1}(B)) (w_i = first r flag vectors), lex order;
a node is pruned iff some g in G = <gens> has a determined key prefix with K(B^g) < K(B).
Component 0 per coset g_u S0 (S0 = Stab(w0)): s_w0(B^{g_u s}) = t_u(s_u) o s, min = canon0(t_u(s_u)); ties
(t_u(s_u) o s = s0) are exactly s in h_a J(s0) (a = t_u(s_u), h_a: a o h_a = canon0(a), J(c) = Stab_S0(c)), and
for those g = g_u o h_a o k the components i >= 1 are compared explicitly: s_wi(B^g) = T_{g,i} s_{g wi}(B).
Group products: (x o y)(p) = x(y(p)); action on syndromes (s o h)(z) = s(h z), so s o (x o y) = (s o x) o y.
File 'LTSH': header 'LTSH r m0 c0 nO nS0 nG nCls'; line of key 'c_i m_i' (i<r); canon0 (2^m0); hS0 (2^m0);
nCls lines 'c |J| J...'; mulS0 (nS0 lines of nS0 ints); nO lines 'c_u t_u rows(m0) comp[u][0..nS0-1]'
(u = w0 first, identity); nG lines (only if r>1) 'c_{g w1} rows(m1) c_{g w2} rows(m2) ...'.
Usage: prep3(gens, m, instance, out, flag, r[, G])  /  symprep3.py CI INSTANCE OUT FLAGFILE R"""
import sys, pickle
sys.path.insert(0, '<HOME>/c72/explore/src')
from common import *
from symprep import closure, coords_fn
from symprep2 import make_ap

def prep3(gens, m, instance, out, flag, r, G=None, verbose=True, key=None):
    ap = make_ap(m)
    meta = [list(map(int, l.split())) for l in open(instance + '.meta')]
    idx = {row[0]: k for k, row in enumerate(meta)}
    key = list(key[:r]) if key is not None else flag[:r]
    for w in key: assert w in idx, "key word without constraint"
    if G is None: G = closure(gens, m)
    G = [tuple(g) for g in G]
    gidx = {g: k for k, g in enumerate(G)}
    comp2 = lambda x, y: tuple(x[y[p]] for p in range(m))       # x o y
    w0 = key[0]; c0 = idx[w0]; ub0 = meta[c0][1:]; m0 = len(ub0); co0 = coords_fn(ub0)
    S0 = [g for g in G if ap(g, w0) == w0]; s0idx = {g: k for k, g in enumerate(S0)}
    # action of S0 on w0-syndromes: (s o h)_j = parity(row_h[j] & s), row_h[j] = coords0(h ub0_j)
    acts = [[co0(ap(h, ub0[j])) for j in range(m0)] for h in S0]
    def act(rows, s):
        o = 0
        for j, rr in enumerate(rows):
            if bin(rr & s).count('1') & 1: o |= 1 << j
        return o
    canon0 = [-1] * (1 << m0); hS0 = [-1] * (1 << m0)
    for s in range(1 << m0):
        if canon0[s] >= 0: continue
        imgs = [act(rows, s) for rows in acts]
        orb = {}
        for hi, x in enumerate(imgs): orb.setdefault(x, hi)       # x = s o S0[hi]
        mn = min(orb)
        # for each element x = s o h_x of the orbit: an element mapping x to mn is h_x^{-1} o h_mn
        inv = {}
        for x, hx in orb.items():
            if x == mn: canon0[x] = mn; continue
            canon0[x] = mn
        # compute hS0[x] by direct search (orbit small): first h with x o h == mn
        for x in orb:
            for hi, rows in enumerate(acts):
                if act(rows, x) == mn: hS0[x] = hi; break
    classes = sorted(set(canon0))
    Jl = {}
    for c in classes:
        Jl[c] = [hi for hi, rows in enumerate(acts) if act(rows, c) == c]
    nS0 = len(S0)
    mul = [[s0idx[comp2(S0[a], S0[b])] for b in range(nS0)] for a in range(nS0)]
    # orbit of w0 with coset reps g_u (u = w0 first: identity)
    idt = tuple(range(m))
    reps = {w0: idt}
    for g in G:
        u = ap(g, w0)
        if u not in reps: reps[u] = g
    order = [w0] + [u for u in reps if u != w0]
    lines_u = []
    for u in order:
        gu = reps[u]; cu = idx[u]; cou = coords_fn(meta[cu][1:])
        rows = [cou(ap(gu, ub0[j])) for j in range(m0)]
        compu = [gidx[comp2(gu, h)] for h in S0]
        lines_u.append(' '.join(map(str, [cu] + rows + compu)))
    lines_g = []
    if r > 1:
        cinfo = [(idx[w], meta[idx[w]][1:]) for w in key]
        cache = {}
        for g in G:
            parts = []
            for i in range(1, r):
                v = ap(g, key[i]); c = idx[v]
                if c not in cache: cache[c] = coords_fn(meta[c][1:])
                co = cache[c]; ub = cinfo[i][1]
                parts.append(str(c)); parts += [str(co(ap(g, ub[j]))) for j in range(len(ub))]
            lines_g.append(' '.join(parts))
    with open(out, 'w') as f:
        f.write(f"LTSH {r} {m0} {c0} {len(order)} {nS0} {len(G)} {len(classes)}\n")
        f.write(' '.join(f"{idx[w]} {len(meta[idx[w]]) - 1}" for w in key) + '\n')
        f.write(' '.join(map(str, canon0)) + '\n')
        f.write(' '.join(map(str, hS0)) + '\n')
        for c in classes: f.write(' '.join(map(str, [c, len(Jl[c])] + Jl[c])) + '\n')
        for a in range(nS0): f.write(' '.join(map(str, mul[a])) + '\n')
        f.write('\n'.join(lines_u) + '\n')
        if lines_g: f.write('\n'.join(lines_g) + '\n')
    if verbose:
        print(f"LTSH: r={r} |G|={len(G)} |orbit(w0)|={len(order)} |S0|={nS0} classes={len(classes)} "
              f"max|J|={max(len(v) for v in Jl.values())}")
    return G

if __name__ == '__main__':
    ci = int(sys.argv[1]); inst = sys.argv[2]; out = sys.argv[3]; flagf = sys.argv[4]; r = int(sys.argv[5])
    res = pickle.load(open('<HOME>/c72/c2par/invs.pkl', 'rb'))
    flag = [int(x) for x in [l for l in open(flagf) if l.startswith('FLAG')][0].split()[1:]]
    prep3(res[ci]['perms'], 36, inst, out, flag, r)
