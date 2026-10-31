"""QR48 positive control (length 48, d = 12) for the whole pipeline, with the audit's own tools.
(Y, bb) from the control48v4.py preamble (QR48 and a free Klein four-group in PSL(2,47)); instance by
lwprep.build (order given); solutions by lwe (run-source build) AND by the naive engine (must agree, incl. node
counts); every solution checked as a genuine code: self-dual [48,24], doubly even, alpha/beta-invariant, minimum
weight exactly 12 by enumerating all 2^24 codewords.  Usage: qr48_control.py ORDER OUTDIR"""
import sys, subprocess, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np
order, outdir = sys.argv[1], sys.argv[2]
src = open(HERE + '/../../../model/control48v4.py').read().split("S = setup(Ygens, bb")[0]
exec(src)
sys.path.insert(0, HERE + '/../../../model')
from lwprep import build, export
S = HERE + '/../scripts'
m = 24; K = 12; A = (1 << m) - 1
L = build(Ygens, bb, m=24, d=12, order=order)
fn = f'{outdir}/qr48_{order}.txt'
export(L, fn)
pickle.dump(dict(w=L['w'], free=L['free'], entf=L['entf'], N=L['N'], Ygens=Ygens, bb=list(bb)), open(fn + '.pkl', 'wb'))
o1 = subprocess.run([f'{S}/lwe_box', fn], capture_output=True, text=True).stdout
o2 = subprocess.run([f'{S}/naive', fn, 'count'], capture_output=True, text=True).stdout
s1 = sorted(l.split()[1] for l in o1.split('\n') if l.startswith('SOLUTION'))
s2 = sorted(l.split()[1] for l in o2.split('\n') if l.startswith('SOLUTION'))
l1 = [l.split()[1:] for l in o1.split('\n') if l.startswith('LEVEL')]
l2 = [l.split()[1:] for l in o2.split('\n') if l.startswith('LEVEL')]
print(f'order {order}: N {L["N"]}, lwe solutions {len(s1)}, naive solutions {len(s2)}, identical sets {s1 == s2}, identical LEVEL lines {l1 == l2}', flush=True)
# genuine-code check of every solution
w = L['w']; E = L['E']; entf = L['entf']
piv = {}
for k in range(K):
    v, t = w[k], 1 << k
    for b, (r, tt) in list(piv.items()):
        if (v >> b) & 1: v ^= r; t ^= tt
    hb = v.bit_length() - 1
    for b2, (r, tt) in list(piv.items()):
        if (r >> hb) & 1: piv[b2] = (r ^ v, tt ^ t)
    piv[hb] = (v, t)
d = [0] * K
for b, (r, t) in piv.items():
    for j in range(K):
        if (t >> j) & 1: d[j] |= 1 << b
def par(x): return bin(x).count('1') & 1
def ap(p, x):
    o = 0
    for i in range(m):
        if (x >> i) & 1: o |= 1 << p[i]
    return o
good = 0; mins = {}
for sx in s1:
    X = int(sx, 16)
    G = [[0] * K for _ in range(K)]
    for e, (i, j) in enumerate(E):
        vm, c = entf[e]; G[i][j] = G[j][i] = par(vm & X) ^ c
    rows = [w[k] | (w[k] << m) for k in range(K)]
    for a in range(K):
        x = 0
        for j in range(K):
            if G[a][j]: x ^= d[j]
        rows.append(x | ((x ^ w[a]) << m))
    W = np.zeros(1, dtype=np.uint64)
    for r in rows: W = np.concatenate([W, W ^ np.uint64(r)])
    wts = np.bitwise_count(W)
    Wset = set(int(z) for z in W)
    ok = (len(Wset) == 1 << 24 and (wts % 4 == 0).all() and all(par(r1 & r2) == 0 for r1 in rows for r2 in rows)
          and all(((r >> m) | ((r & A) << m)) in Wset for r in rows)
          and all((ap(bb, r & A) | (ap(bb, r >> m) << m)) in Wset for r in rows))
    mn = int(wts[1:].min())
    mins[mn] = mins.get(mn, 0) + 1
    good += ok and mn == 12
print(f'order {order}: genuine self-dual doubly-even V-invariant codes with minimum weight 12: {good} of {len(s1)}; minimum weights {mins}', flush=True)
