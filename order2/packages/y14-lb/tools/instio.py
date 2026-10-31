"""Read/write level-wise instances (lwe format of c2explore/src/mkinst.py export) and basic F2 linear algebra on
Python ints.  A constraint: dict(lv, wt, m, forms[list of int masks over N vars], consts[list of 0/1], bad[list],
y, ub).  Reachable syndromes: if the forms have a linear relation lam (sum lam_s forms_s = 0), the value
lam.s = lam.consts is constant; nreach = 2^(m - #relations), nbadr = #bad syndromes satisfying all relations."""
import math


def read_inst(fn, meta=True):
    tok = open(fn).read().split()
    p = 0

    def nxt():
        nonlocal p
        p += 1
        return tok[p - 1]
    N, NLEV, NC = int(nxt()), int(nxt()), int(nxt())
    vstart = [int(nxt()) for _ in range(NLEV + 1)]
    cons = []
    for c in range(NC):
        lv, wt, m, nb = int(nxt()), int(nxt()), int(nxt()), int(nxt())
        forms, consts = [], []
        for s in range(m):
            forms.append(int(nxt(), 16))
            consts.append(int(nxt()))
        bad = [int(nxt()) for _ in range(nb)]
        cons.append(dict(lv=lv, wt=wt, m=m, forms=forms, consts=consts, bad=bad))
    if meta:
        try:
            lines = open(fn + '.meta').read().strip().split('\n')
            assert len(lines) == NC
            for c, l in zip(cons, lines):
                v = list(map(int, l.split()))
                c['y'] = v[0]
                c['ub'] = v[1:]
        except FileNotFoundError:
            pass
    return dict(N=N, NLEV=NLEV, vstart=vstart, cons=cons)


def write_inst(fn, N, vstart, cons, write_meta=True):
    """cons must be sorted by lv; each needs lv, wt, forms, consts, bad (and y, ub for meta)."""
    NLEV = len(vstart) - 1
    out = [f"{N} {NLEV} {len(cons)}", ' '.join(map(str, vstart))]
    for c in cons:
        out.append(f"{c['lv']} {c['wt']} {len(c['forms'])} {len(c['bad'])}")
        for f, k in zip(c['forms'], c['consts']):
            out.append(f"{f:x} {k}")
        out.append(' '.join(map(str, c['bad'])))
    open(fn, 'w').write('\n'.join(out) + '\n')
    if write_meta and all('y' in c for c in cons):
        open(fn + '.meta', 'w').write('\n'.join(' '.join(map(str, [c['y']] + list(c['ub']))) for c in cons) + '\n')


class Basis:
    """Incremental F2 row-echelon basis of int vectors (pivot = highest bit), with reduce()."""
    def __init__(self):
        self.piv = {}      # pivot bit -> vector (fully reduced on other pivots is not required)

    def reduce(self, v):
        piv = self.piv
        while v:
            h = v.bit_length() - 1
            b = piv.get(h)
            if b is None:
                return v
            v ^= b
        return 0

    def add(self, v):
        v = self.reduce(v)
        if v:
            self.piv[v.bit_length() - 1] = v
            return 1
        return 0

    def __len__(self):
        return len(self.piv)

    def copy(self):
        b = Basis()
        b.piv = dict(self.piv)
        return b


def relations(forms):
    """Basis of lam (bitmask over form indices) with sum lam_s forms_s = 0."""
    piv = {}
    rel = []
    for i, v in enumerate(forms):
        c = 1 << i
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h][0]
                c ^= piv[h][1]
            else:
                piv[h] = (v, c)
                break
        if not v:
            rel.append(c)
    return rel


def pass_prob(c):
    """Fraction of reachable syndromes that are good (reachable = consistent with the constant relations)."""
    rel = relations(c['forms'])
    m = len(c['forms'])
    cst = []
    for lam in rel:
        k = 0
        for i in range(m):
            if (lam >> i) & 1:
                k ^= c['consts'][i]
        cst.append(k)
    nreach = 1 << (m - len(rel))
    nb = 0
    for b in c['bad']:
        if all((bin(b & lam).count('1') & 1) == k for lam, k in zip(rel, cst)):
            nb += 1
    return (nreach - nb) / nreach, nreach, nb, len(rel)
