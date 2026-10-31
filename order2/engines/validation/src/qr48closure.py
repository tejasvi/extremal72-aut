"""qr48closure.py LOGDIR : H-closure check of the rc11 representatives of every QR48 key configuration (logs
LOGDIR/qr/<tag>_lwe11rc11_lb.log), against the plain solution set; configurations from tmp/qr48lb/cfg_*.pkl. Based on QR48 key controls for rc11 / lwe11b5 (bit-granular LTS), following struct's
struct/src/qr48keyb.py (same seeds, same groups, keys and random key bases; files under alg/tmp/qr48lb/).  KEYMODE is
'orbit' (PointStab and Rand1, r = 1, 2, 3, 6) or 'fixed' (three Stab(y) groups, r = 1, 2, 3, 6).  Per configuration:
the prototype lwe10b without and with LTSBFILE, rc11 / lwe11b5 with LTSBFILE (output must equal the prototype's,
LBPRUNE line included), rc11 with LWE11CHECK, rc11 without LTSBFILE (= the prototype without it); the H-closure of the
rc11 representatives must equal the plain solution set (rc9, no symmetry) with nothing outside.
struct's modules are imported read-only (no bytecode written)."""
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
import os, pickle, random, subprocess, re, hashlib, time
from common import *
import mkinst
from qrctl import setup
from nautyaut import aut_gens
from symprep import closure, ap, coords_fn
from symprep3 import prep3
from ltsblib import make_ltsb
from instio import read_inst as RI

ALG = '<HOME>/c72/c2opt/alg'
TMP = f'{ALG}/tmp/qr48lb'
os.makedirs(TMP, exist_ok=True)
env = dict(os.environ, TMPDIR=f'{ALG}/tmp')
BIN = dict(proto=f'{ALG}/build11/lwe10b', rc11=f'{ALG}/build11/lwe11', b5=f'{ALG}/build11/lwe11b', rc9=f'{ALG}/frozen_rc9/lwe11')
logdir = sys.argv[1]
keymode = 'closure'
mode, flagname = 'full', 'qr'
t0 = time.time()
S = setup(47); m = 24; d = 12
Yg = S['Ygens']
gens = aut_gens(Yg, m)
G = closure(gens, m)
D = pickle.load(open('<HOME>/c72/c2opt/struct/inst/qr48.pkl', 'rb'))
w = D['L']['w']
L = mkinst.build(Yg, w, m=m, d=d, verbose=False)
inst = f'{TMP}/qr48k_{mode}_{flagname}_{keymode}.txt'
mkinst.export(L, inst)


def run(eng, fi, extra):
    p = subprocess.run([BIN[eng], fi], capture_output=True, text=True, env=dict(env, **extra))
    return p.stdout, p.stderr


def core(out):
    return [re.sub(r'time [0-9]*s', '', l) for l in out.split('\n') if l.startswith(('LEVEL', 'DONE', 'SOL', 'LBPRUNE'))]


def reps_of(out):
    return [int(l.split()[1], 16) for l in out.split('\n') if l.startswith('SOLUTION')]


plain_out, _ = run('rc9', inst, {})
solf = set(reps_of(plain_out))
print(f"keymode {keymode}: |Aut(Y48)| = {len(G)}, plain solutions {len(solf)}, instance sha {hashlib.sha256(open(inst, 'rb').read()).hexdigest()[:16]} ({time.time() - t0:.0f} s)", flush=True)
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


def image(a, cw):
    Gm = [[0] * K for _ in range(K)]
    for e, (i, j) in enumerate(E):
        vm, c = entf[e]; v = (pc(vm & a) & 1) ^ c; Gm[i][j] = Gm[j][i] = v
    Gv = 0
    for i in range(K):
        ci = cw[i]; rowv = [0] * K
        for p in range(K):
            if (ci >> p) & 1:
                for q in range(K): rowv[q] ^= Gm[p][q]
        for j in range(i, K):
            cj = cw[j]; v = 0
            for q in range(K):
                if (cj >> q) & 1: v ^= rowv[q]
            if v: Gv |= 1 << eidx[(i, j)]
    for b, g_ in gp.items():
        if (Gv >> b) & 1: Gv ^= g_
    a2 = 0
    for k, e in enumerate(free):
        if (Gv >> e) & 1: a2 |= 1 << k
    return a2


def closure_check(sols, hgens):
    gw = [[co(ap(g, w[i], m)) for i in range(K)] for g in hgens]
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
    return len(cover), outside, cover == solf



for km in ('orbit', 'fixed'):
    D = pickle.load(open(f'{TMP}/cfg_{km}.pkl', 'rb'))
    if set(D['solf']) != solf: print('plain set differs from the prepared one'); sys.exit(1)
    for c in D['CFG']:
        f = f"{logdir}/qr/{c['tag']}_lwe11rc11_lb.log"
        reps = reps_of(open(f).read())
        nc, outside, eq = closure_check(reps, c['hgens'])
        print(f"{c['tag']}: |H|={c['H']} r={c['r']} reps {len(reps)} H-closure {nc} outside {outside} equals plain set {eq}", flush=True)
