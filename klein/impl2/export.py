"""Export an Instance (with order set) to the C engine format; decode/verify solutions."""
import sys, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gf2 import *
from autgroup import apply_perm_vec
from order import con_info

def export(I, path):
    k, N = I.k, I.N
    lines = []
    lines.append("%d %d" % (k, N))
    vstart = [0] * (k + 1)
    for t in range(k):
        vstart[t + 1] = vstart[t] + I.k_t[t]
    assert vstart[k] == N
    assert I.var_level == sorted(I.var_level)
    lines.append(" ".join(map(str, vstart)))
    for t in range(k):
        for l in range(t, k):
            e = I.idx[(t, l)]
            const = (I.part >> e) & 1
            vs = [s for s in range(N) if (I.H[s] >> e) & 1]
            lines.append("%d %d %s" % (const, len(vs), " ".join(map(str, vs))))
    cons = export_cons(I)
    lines.append("%d" % len(cons))
    for lev, _, w, cm, d, bad, rep in cons:
        lines.append("%d %d %d %d %s %d %s" % (lev, w, cm, len(d), " ".join(map(str, d)), len(bad),
                                               " ".join(map(str, bad))))
    open(path, "w").write("\n".join(lines) + "\n")
    return vstart

def export_cons(I):
    """Constraint list in engine order: (level, -info, weight, coords of representative, d-vectors, bad, rep)."""
    cons = []
    for c, lev in zip(I.cons, I.con_level):
        y = c['y']
        yb = apply_perm_vec(I.beta, y)
        cy, cyb = I.coords(y), I.coords(yb)
        if cy.bit_length() - 1 == lev:
            rep, cc = y, c
        else:
            assert cyb.bit_length() - 1 == lev
            rep = yb
            cc = I._constraint(yb)
            assert cc['nbad'] == c['nbad'] and cc['m'] == c['m']
        cm = I.coords(rep)
        d = [I.coords(x) for x in cc['X']]
        cons.append((lev, -con_info(cc), cc['w'], cm, d, cc['bad'], rep))
    cons.sort(key=lambda r: (r[0], r[1]))
    return cons

def gram_from_x(I, xbits):
    """Gram matrix G[i][l] = B(w_i, w_l) for the solution x (list of 0/1 of length N)."""
    v = I.part
    for s, b in enumerate(xbits):
        if b:
            v ^= I.H[s]
    k = I.k
    G = [[(v >> I.idx[(i, l)]) & 1 for l in range(k)] for i in range(k)]
    return G

def solve_z(I, row):
    """Find z in F2^n2 with <z, w_l> = row[l] for all l."""
    # linear system: unknown z (n2 bits); equations: parity(z & w_l) = row[l]
    from structure import solve_affine
    eqs = [(I.w[l], row[l]) for l in range(I.k)]
    sol = solve_affine(eqs, I.n2)
    assert sol is not None
    return sol[0]

def build_code(I, G):
    """Generator rows (ints of length 2*n2): first half z, second half z+y."""
    n2 = I.n2
    rows = []
    for i in range(I.k):
        z = solve_z(I, G[i])
        rows.append(z | ((z ^ I.w[i]) << n2))
    for i in range(I.k):
        rows.append(I.w[i] | (I.w[i] << n2))
    return rows

def perm_a(n2):
    return [i + n2 if i < n2 else i - n2 for i in range(2 * n2)]

def perm_b(I):
    n2 = I.n2
    return [I.beta[i] if i < n2 else I.beta[i - n2] + n2 for i in range(2 * n2)]

def verify_code(I, rows, dmin, full_distance=True):
    n = 2 * I.n2
    ok = True
    info = {}
    info['rank'] = rank(rows)
    info['selforth'] = all(dot(x, y) == 0 for x in rows for y in rows)
    info['doubly_even'] = all(popcount(x) % 4 == 0 for x in rows)
    S = Span(rows)
    info['inv_a'] = all(S.contains(apply_perm_vec(perm_a(I.n2), r)) for r in rows)
    info['inv_b'] = all(S.contains(apply_perm_vec(perm_b(I), r)) for r in rows)
    if full_distance:
        wd = weight_distribution(echelon(rows), n)
        info['d'] = min(i for i in range(1, n + 1) if wd[i])
        info['wd_low'] = {i: int(wd[i]) for i in range(1, min(n, dmin + 8) + 1) if wd[i]}
    return info
