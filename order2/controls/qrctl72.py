"""QR72 (d = 12) planted control for the plain-C2 level-wise model (72-bit vectors -> pure linear algebra).
Builds Y = contracted fixed code of the fpf involution alpha: x -> -1/x, QR72's own gauge-normalised assignment,
checks it satisfies all constraints, then pins all variables of levels < PL and runs the engine on the rest.
Usage: qrctl72.py OUTPREFIX PL [PL ...]"""
import sys, pickle, subprocess, os
sys.path.insert(0, '<HOME>/c72/explore/src')
from common import pc, span_np
import numpy as np
import mkinst
from qrctl import ext_qr, mobius_alpha, check_assignment

def solve_lin(rows, target):
    """rows: list of ints (vectors); find coefficient mask lam with XOR_{i in lam} rows[i] = target (or None)."""
    piv = {}
    for i, r in enumerate(rows):
        v = r; c = 1 << i
        for b in sorted(piv, reverse=True):
            if (v >> b) & 1: v ^= piv[b][0]; c ^= piv[b][1]
        if v: piv[v.bit_length() - 1] = (v, c)
    v = target; c = 0
    for b in sorted(piv, reverse=True):
        if (v >> b) & 1: v ^= piv[b][0]; c ^= piv[b][1]
    return c if v == 0 else None

p = 71; n = 72; m = 36
Cg = ext_qr(p); alpha = mobius_alpha(p)
def ap(perm, w):
    o = 0
    for i in range(n):
        if (w >> i) & 1: o |= 1 << perm[i]
    return o
pairs = []; used = set()
for x in range(n):
    if x in used: continue
    pairs.append((x, alpha[x])); used |= {x, alpha[x]}
def proj(w):
    y = 0; z = 0
    for i, (a, b) in enumerate(pairs):
        ai = (w >> a) & 1; bi = (w >> b) & 1
        if ai ^ bi: y |= 1 << i
        if ai: z |= 1 << i
    return y, z
# fixed subcode: lam with sum lam_i (g_i + alpha g_i) = 0
diffs = [g ^ ap(alpha, g) for g in Cg]
# kernel via elimination with tracking
piv = {}; kern = []
for i, r in enumerate(diffs):
    v = r; c = 1 << i
    for b in sorted(piv, reverse=True):
        if (v >> b) & 1: v ^= piv[b][0]; c ^= piv[b][1]
    if v: piv[v.bit_length() - 1] = (v, c)
    else: kern.append(c)
fixed = []
for c in kern:
    w = 0
    for i in range(len(Cg)):
        if (c >> i) & 1: w ^= Cg[i]
    fixed.append(w)
Ygens = [proj(w)[1] for w in fixed]
assert all(proj(w)[0] == 0 for w in fixed) and len(Ygens) == 18
Yw = span_np(Ygens); yw = np.bitwise_count(Yw)
print("QR72: dim fixed", len(Ygens), " d(Y) =", int(yw[yw > 0].min()), " low weights",
      {int(k): int(v) for k, v in zip(*np.unique(yw, return_counts=True)) if 0 < k < 12}, flush=True)
d = 12
Yall = Yw.tolist(); low = set(y for y in Yall if 0 < pc(y) < d)
w = []; spanset = {0}
while len(w) < 18:
    best = None
    cands = [y for y in low if y not in spanset] or [y for y in Yall if y not in spanset]
    for y in cands[:6000]:
        key = (sum(1 for s in spanset if (s ^ y) in low), -pc(y))
        if best is None or key > best[0]: best = (key, y)
    w.append(best[1]); spanset |= {s ^ best[1] for s in spanset}
L = mkinst.build(Ygens, w, m=36, d=d)
outp = sys.argv[1]
mkinst.export(L, outp + '.txt')
# own B: z(w_k) = z-part of a codeword with y-part w_k
ys = [proj(g)[0] for g in Cg]
zw = []
for k in range(18):
    lam = solve_lin(ys, w[k]); assert lam is not None
    cw = 0
    for i in range(len(Cg)):
        if (lam >> i) & 1: cw ^= Cg[i]
    y_, z_ = proj(cw); assert y_ == w[k]; zw.append(z_)
E = L['E']; entf = L['entf']; free = L['free']; N = L['N']
Gq = {(i, j): pc(zw[i] & w[j]) & 1 for (i, j) in E}
eidx = {e: k for k, e in enumerate(E)}
gauges = []
for q in range(36):
    g = 0
    for (i, j) in E:
        if ((w[i] & w[j]) >> q) & 1: g |= 1 << eidx[(i, j)]
    gauges.append(g)
gp = {}
for g in gauges:
    for b in sorted(gp):
        if (g >> b) & 1: g ^= gp[b]
    if g:
        b = (g & -g).bit_length() - 1
        for b2 in list(gp):
            if (gp[b2] >> b) & 1: gp[b2] ^= g
        gp[b] = g
Gv = 0
for e, v in Gq.items():
    if v: Gv |= 1 << eidx[e]
for b, g in gp.items():
    if (Gv >> b) & 1: Gv ^= g
a = 0
for k, e in enumerate(free):
    if (Gv >> e) & 1: a |= 1 << k
badrep = sum(1 for e in range(len(E)) if ((pc(entf[e][0] & a) & 1) ^ entf[e][1]) != ((Gv >> e) & 1))
print("own form reproduced:", badrep == 0, " violated constraints by own form:", check_assignment(L, a), flush=True)
level = L['level']
for PL in [int(x) for x in sys.argv[2:]]:
    cons = list(L['cons'])
    pinned = [v for v in range(N) if level[v] < PL]
    for v in pinned: cons.append((level[v], 0, [(1 << v, 0)], [1 - ((a >> v) & 1)]))
    L2 = dict(L); L2['cons'] = cons
    fn = f"{outp}_pin{PL}.txt"; mkinst.export(L2, fn)
    out = subprocess.run(['timeout', '1800', '<HOME>/c72/explore/src/lwe2', fn], capture_output=True, text=True,
                         env=dict(os.environ, TMPDIR='<HOME>/c72/explore/tmp')).stdout
    sols = [int(l.split()[1], 16) for l in out.split('\n') if l.startswith('SOLUTION')]
    done = [l for l in out.split('\n') if l.startswith('DONE')]
    import random as _r
    samp = sols if len(sols) <= 200 else _r.Random(1).sample(sols, 200)
    print(f"pin levels <{PL}: {len(pinned)} pinned, {N - len(pinned)} free: solutions {len(sols)}, own found {a in sols}, "
          f"sampled {len(samp)} solutions satisfy all constraints {all(check_assignment(L, s) == 0 for s in samp)}, {done[0] if done else 'TIMEOUT'}", flush=True)
