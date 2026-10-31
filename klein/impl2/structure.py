"""Per-instance structure: beta-module type, contracted fixed code D, parameter/gauge dimensions."""
import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import apply_perm_vec

def coords(basis, v):
    """Coordinates of v in basis (list of ints) -- via solving; returns int bitmask over basis index."""
    # build augmented elimination
    k = len(basis)
    rows = [(b, 1 << i) for i, b in enumerate(basis)]
    piv = []
    for b, tag in rows:
        for p, (pb, pt) in piv:
            if (b >> p) & 1:
                b ^= pb; tag ^= pt
        if b:
            piv.append((b.bit_length() - 1, (b, tag)))
    tag = 0
    for p, (pb, pt) in piv:
        if (v >> p) & 1:
            v ^= pb; tag ^= pt
    assert v == 0
    return tag

def solve_affine(eqs, nvars):
    """eqs: list of (mask, rhs). Return (particular solution mask, list of homogeneous basis masks) or None."""
    piv = []  # (pivot bit, mask, rhs)
    for m, r in eqs:
        for p, pm, pr in piv:
            if (m >> p) & 1:
                m ^= pm; r ^= pr
        if m == 0:
            if r:
                return None
            continue
        p = m.bit_length() - 1
        # reduce others
        npiv = []
        for q, qm, qr in piv:
            if (qm >> p) & 1:
                qm ^= m; qr ^= r
            npiv.append((q, qm, qr))
        piv = npiv + [(p, m, r)]
    pivbits = {p for p, _, _ in piv}
    part = 0
    for p, m, r in piv:
        if r:
            part |= 1 << p
    free = [i for i in range(nvars) if i not in pivbits]
    hom = []
    for f in free:
        v = 1 << f
        for p, m, r in piv:
            if (m >> f) & 1:
                v |= 1 << p
        hom.append(v)
    return part, hom

class SymParam:
    """Symmetric bilinear forms on Y (basis yb) as 171-bit masks: var index for (i<=j)."""
    def __init__(self, k):
        self.k = k
        self.idx = {}
        t = 0
        for i in range(k):
            for j in range(i, k):
                self.idx[(i, j)] = t; self.idx[(j, i)] = t
                t += 1
        self.nvars = t
    def form_value_mask(self, ci, cj):
        """Mask of variables whose XOR gives B(y,y') with y=sum ci, y'=sum cj (coordinate masks)."""
        m = 0
        k = self.k
        for i in range(k):
            if (ci >> i) & 1:
                for j in range(k):
                    if (cj >> j) & 1:
                        m ^= 1 << self.idx[(i, j)]
        return m

def instance_structure(Ybasis, beta, n2=36):
    k = len(Ybasis)
    yb = echelon(Ybasis)
    sp = SymParam(k)
    bimg = [apply_perm_vec(beta, y) for y in yb]
    bco = [coords(yb, v) for v in bimg]
    one = (1 << n2) - 1
    cone = coords(yb, one)
    eqs = []
    # beta invariance: B(beta y_i, beta y_j) = B(y_i, y_j)
    for i in range(k):
        for j in range(i, k):
            m = sp.form_value_mask(bco[i], bco[j]) ^ (1 << sp.idx[(i, j)])
            eqs.append((m, 0))
    # doubly even: B(y_i,y_i) + B(y_i,1) = wt(y_i)/2
    for i in range(k):
        m = (1 << sp.idx[(i, i)]) ^ sp.form_value_mask(1 << i, cone)
        eqs.append((m, (popcount(yb[i]) // 2) & 1))
    sol = solve_affine(eqs, sp.nvars)
    assert sol is not None
    part, hom = sol
    # gauge: T beta-invariant or T+beta T = all
    orbits = []
    seen = set()
    for i in range(n2):
        if i not in seen:
            orbits.append((i, beta[i])); seen |= {i, beta[i]}
    gauge = []
    def DT(Tmask):
        m = 0
        for i in range(k):
            for j in range(i, k):
                if popcount(yb[i] & yb[j] & Tmask) & 1:
                    m |= 1 << sp.idx[(i, j)]
        return m
    for (i, j) in orbits:
        gauge.append(DT((1 << i) | (1 << j)))
    trans = 0
    for (i, j) in orbits:
        trans |= 1 << i
    gauge.append(DT(trans))
    # rank of gauge inside hom space
    hs = Span(hom)
    assert all(hs.contains(g) for g in gauge)
    grank = rank(gauge)
    # module structure
    r = rank([yb[i] ^ bimg[i] for i in range(k)])
    # fixed subcode
    fix = solve_affine([], 0)
    # Y^beta: kernel of (1+beta) on Y
    # compute via coordinates: (1+beta) as matrix on coords
    rows = []
    M = [(1 << i) ^ bco[i] for i in range(k)]  # image coords of y_i under 1+beta
    # kernel of map c -> sum c_i M_i
    eqs2 = []
    for bit in range(k):
        m = 0
        for i in range(k):
            if (M[i] >> bit) & 1:
                m |= 1 << i
        eqs2.append((m, 0))
    _, ker = solve_affine(eqs2, k)
    Yfix = []
    for c in ker:
        v = 0
        for i in range(k):
            if (c >> i) & 1:
                v ^= yb[i]
        Yfix.append(v)
    reps = [i for (i, j) in orbits]
    D = []
    for v in Yfix:
        d = 0
        for t, i in enumerate(reps):
            if (v >> i) & 1:
                d |= 1 << t
        D.append(d)
    wdD = weight_distribution(D, len(reps)) if D else None
    return dict(rank1beta=r, dimfix=len(Yfix), nparam=len(hom), gauge=grank,
                eff=len(hom) - grank, wdD={i: int(x) for i, x in enumerate(wdD) if x})

if __name__ == '__main__':
    codes = json.load(open(HERE + '/data/codes41.json'))
    fpf = json.load(open(HERE + '/data/fpf41.json'))
    out = []
    for c, f in zip(codes, fpf):
        for ci, cl in enumerate(f['classes']):
            s = instance_structure(c['basis'], cl['beta'])
            s.update(code=c['idx'], cls=ci, A8=c['wd']['8'], cent=cl['centralizer'])
            print(s, flush=True)
            out.append(s)
    json.dump(out, open(HERE + '/data/structure.json', 'w'))
