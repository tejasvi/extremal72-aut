"""Augment an instance with PROJECTED (partial-syndrome) constraints and remap its LTSH file.
For a constraint c at level lv and t in [lv-DEPTH, lv-1]: P = basis of the annihilator of the future part of the
forms (variables of levels t+1..lv); the projected syndrome u = P s depends only on levels <= t; u is bad iff every
REACHABLE s with P s = u is bad.  Such a constraint is implied by c, so the solution set is unchanged; it only
filters level-t children earlier.  Only projections with a nonempty bad set are added (level t, after the
original level-t constraints in file order; the engine reorders within a level anyway).
Usage: addproj.py INST OUT DEPTH [LTSH_IN LTSH_OUT]"""
import sys
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *


def projections(I, depth):
    cons = I['cons']; vs = I['vstart']
    out = []      # (t, newcon)
    for ci, c in enumerate(cons):
        lv = c['lv']; m = c['m']; badset = set(c['bad'])
        allrel = relations(c['forms'])
        cst = [sum(c['consts'][i] for i in range(m) if (lam >> i) & 1) & 1 for lam in allrel]
        reach = [s for s in range(1 << m) if all((bin(lam & s).count('1') & 1) == k for lam, k in zip(allrel, cst))]
        for t in range(lv - 1, max(-1, lv - 1 - depth), -1):
            fm = ((1 << vs[lv + 1]) - 1) ^ ((1 << vs[t + 1]) - 1)
            rel = relations([f & fm for f in c['forms']])
            if not rel:
                break
            fib = {}
            for s in reach:
                u = 0
                for i, lam in enumerate(rel):
                    u |= (bin(lam & s).count('1') & 1) << i
                fib.setdefault(u, []).append(s)
            pb = sorted(u for u, ss in fib.items() if all(x in badset for x in ss))
            if not pb:
                break
            forms = []; consts = []
            for lam in rel:
                f = 0; k = 0
                for i in range(m):
                    if (lam >> i) & 1:
                        f ^= c['forms'][i]; k ^= c['consts'][i]
                assert f >> vs[t + 1] == 0
                forms.append(f); consts.append(k)
            out.append((t, dict(lv=t, wt=c['wt'], m=len(forms), forms=forms, consts=consts, bad=pb,
                                y=c.get('y', 0), ub=[], src=ci)))
    return out


def remap_ltsh(fin, fout, newidx):
    tok = open(fin).read().split('\n')
    hdr = tok[0].split(); r = int(hdr[1]); m0 = int(hdr[2]); hdr[3] = str(newidx[int(hdr[3])])
    nO = int(hdr[4]); nS0 = int(hdr[5]); nG = int(hdr[6]); ncls = int(hdr[7])
    keyl = tok[1].split(); ms = []
    for i in range(r):
        keyl[2 * i] = str(newidx[int(keyl[2 * i])]); ms.append(int(keyl[2 * i + 1]))
    lines = [' '.join(hdr), ' '.join(keyl)]
    p = 2
    lines += tok[p:p + 2]; p += 2                    # canon0, hS0
    lines += tok[p:p + ncls]; p += ncls             # classes
    lines += tok[p:p + nS0]; p += nS0               # mul
    for u in range(nO):
        v = tok[p].split(); v[0] = str(newidx[int(v[0])]); lines.append(' '.join(v)); p += 1
    if r > 1:
        for g in range(nG):
            v = tok[p].split(); q = 0
            for i in range(1, r):
                v[q] = str(newidx[int(v[q])]); q += 1 + ms[i]
            assert q == len(v)
            lines.append(' '.join(v)); p += 1
    rest = [l for l in tok[p:] if l.strip()]
    assert not rest, rest[:2]
    open(fout, 'w').write('\n'.join(lines) + '\n')


if __name__ == '__main__':
    fin, fout, depth = sys.argv[1], sys.argv[2], int(sys.argv[3])
    I = read_inst(fin)
    cons = I['cons']
    for c in cons:
        c.setdefault('y', 0); c.setdefault('ub', [])
    pr = projections(I, depth)
    # merge: original constraints keep relative order; projections of level t go after the originals of level t
    merged = []; newidx = {}
    byt = {}
    for t, nc in pr:
        byt.setdefault(t, []).append(nc)
    for t in range(I['NLEV'] + 1):
        for ci, c in enumerate(cons):
            if c['lv'] == t:
                newidx[ci] = len(merged); merged.append(c)
        merged += byt.get(t, [])
    assert len(newidx) == len(cons)
    write_inst(fout, I['N'], I['vstart'], merged, write_meta=False)
    # meta: originals keep their meta lines; projections get 'y' only (not used by the engine)
    open(fout + '.meta', 'w').write('\n'.join(' '.join(map(str, [c['y']] + list(c['ub']))) for c in merged) + '\n')
    cnt = {}
    for t, nc in pr:
        cnt[t] = cnt.get(t, 0) + 1
    print("added projections per level:", sorted(cnt.items()), "total", len(pr))
    if len(sys.argv) > 5:
        remap_ltsh(sys.argv[4], sys.argv[5], newidx)
        print("remapped", sys.argv[4], "->", sys.argv[5])
