"""Validate the LTS symmetry test on the QR48 control: Aut(Y48) via nauty, instance + meta, symfile, lwe3 with
SYMFILE; completeness: the Aut(Y)-orbits (gauge-normalised) of the symmetric solutions must cover all solutions
of the plain complete run (logs/qr48_full.log)."""
import sys, pickle, subprocess, os
import numpy as np
sys.path.insert(0, '<HOME>/c72/explore/src')
from common import *
import mkinst
from qrctl import setup
from nautyaut import aut_gens
from symprep import prep, closure, ap, coords_fn
S = setup(47); m = 24; d = 12
Yg = S['Ygens']
gens = aut_gens(Yg, m)
G = closure(gens, m)
print("Aut(Y48) order", len(G), flush=True)
D = pickle.load(open('<HOME>/c72/explore/inst/qr48.pkl', 'rb'))
w = D['L']['w']
L = mkinst.build(Yg, w, m=m, d=d)
inst = '<HOME>/c72/explore/inst/qr48s.txt'
mkinst.export(L, inst)
prep(gens, m, inst, inst + '.sym', w[0])
env = dict(os.environ, TMPDIR='<HOME>/c72/explore/tmp')
full = subprocess.run(['<HOME>/c72/explore/src/lwe5', inst], capture_output=True, text=True, env=env).stdout
sym = subprocess.run(['<HOME>/c72/explore/src/' + (sys.argv[1] if len(sys.argv) > 1 else 'lwe3'), inst], capture_output=True, text=True, env=dict(env, SYMFILE=inst + '.sym')).stdout
solf = set(int(l.split()[1], 16) for l in full.split('\n') if l.startswith('SOLUTION'))
sols = [int(l.split()[1], 16) for l in sym.split('\n') if l.startswith('SOLUTION')]
print("plain run (rebuilt instance):", len(solf), " symmetric run:", len(sols), flush=True)
print([l for l in sym.split('\n') if l.startswith('DONE')][0])
# orbit closure with gauge normalisation
E = L['E']; entf = L['entf']; free = L['free']; K = len(w)
eidx = {e: k for k, e in enumerate(E)}
co = coords_fn(w)
gp = {}
for q in range(m):
    g_ = 0
    for (i, j) in E:
        if ((w[i] & w[j]) >> q) & 1: g_ |= 1 << eidx[(i, j)]
    for b in sorted(gp):
        if (g_ >> b) & 1: g_ ^= gp[b]
    if g_:
        b = (g_ & -g_).bit_length() - 1
        for b2 in list(gp):
            if (gp[b2] >> b) & 1: gp[b2] ^= g_
        gp[b] = g_
def gram(a):
    Gm = [[0] * K for _ in range(K)]
    for e, (i, j) in enumerate(E):
        vm, c = entf[e]; v = (pc(vm & a) & 1) ^ c; Gm[i][j] = Gm[j][i] = v
    return Gm
def normalise(Gm):
    Gv = 0
    for e, (i, j) in enumerate(E):
        if Gm[i][j]: Gv |= 1 << e
    for b, g_ in gp.items():
        if (Gv >> b) & 1: Gv ^= g_
    a = 0
    for k, e in enumerate(free):
        if (Gv >> e) & 1: a |= 1 << k
    return a
gw = []
for g in gens:
    gw.append([co(ap(g, w[i], m)) for i in range(K)])
def image(a, cw):
    Gm = gram(a)
    Gn = [[0] * K for _ in range(K)]
    for i in range(K):
        ci = cw[i]; rowv = [0] * K
        for p in range(K):
            if (ci >> p) & 1:
                for q in range(K): rowv[q] ^= Gm[p][q]
        for j in range(i, K):
            cj = cw[j]; v = 0
            for q in range(K):
                if (cj >> q) & 1: v ^= rowv[q]
            Gn[i][j] = Gn[j][i] = v
    return normalise(Gn)
# BFS closure of the symmetric solutions under the generators of Aut(Y)
cover = set(sols); fr = list(sols); outside = 0
while fr:
    nf = []
    for a in fr:
        for cw in gw:
            b = image(a, cw)
            if b not in cover:
                cover.add(b); nf.append(b)
                if b not in solf: outside += 1
    fr = nf
print("orbit cover (generator BFS) of symmetric solutions:", len(cover), " images outside plain set:", outside,
      " equals plain solution set:", cover == solf, flush=True)
