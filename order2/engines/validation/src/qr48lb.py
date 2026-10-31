"""qr48lb.py KEYMODE [GROUPS] : QR48 key controls for rc11 / lwe11b5 (bit-granular LTS), following struct's
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
keymode = sys.argv[1]
only = sys.argv[2].split(',') if len(sys.argv) > 2 else None
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


rbr = random.Random(2026)


def rebase(k0, gname, r):
    I = RI(inst); ib = inst + f'.{gname}.r{r}.rb.txt'
    c = [x for x in I['cons'] if x['y'] == k0][0]; ub = c['ub']; mm = len(ub)
    while True:
        T = [rbr.getrandbits(mm) for _ in range(mm)]
        piv = {}
        ok = True
        for v in T:
            for b in sorted(piv, reverse=True):
                if v >> b & 1: v ^= piv[b]
            if not v: ok = False; break
            piv[v.bit_length() - 1] = v
        if ok: break
    nb = []
    for row in T:
        x = 0
        for j in range(mm):
            if row >> j & 1: x ^= ub[j]
        nb.append(x)
    subprocess.run(['<HOME>/c72/venv/bin/python', '-I', '-B', '<HOME>/c72/c2opt/struct/src/rebasis.py', inst, ib, str(k0), ','.join(map(str, nb))], check=True, capture_output=True, env=env)
    return ib


rng = random.Random(11)


def gen_subgroup(elems):
    es = set(map(tuple, elems)); hg = []
    while True:
        hg.append(list(rng.choice(elems)))
        if len(closure(hg, m)) == len(es): return hg


pstab = [g for g in G if g[0] == 0]
FIXEDW = {}
groups = [('PointStab', gen_subgroup(pstab), pstab)]
if keymode == 'fixed':
    lvq = {}
    for (lvl, wt_, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lvq[y] = lvl
    ys = sorted(lvq, key=lambda y: (-lvq[y], y))
    groups = []
    for k, y in enumerate((ys[5], ys[60], ys[200])):
        H = [g for g in G if ap(g, y, m) == y]
        groups.append((f'Stab{k}(y@lv{lvq[y]})', gen_subgroup(H), H))   # k: unique file names (two y share a level)
        FIXEDW[f'Stab{k}(y@lv{lvq[y]})'] = y
if keymode != 'fixed':
    r1 = [list(rng.choice(G))]; groups.append(('Rand1', r1, closure(r1, m)))
allok = True
for gname, hg, H in groups:
    for r in (1, 2, 3, 6):
        hf = inst + f'.{gname}.r{r}.ltsh'
        lv = {}
        for (lvl, wt_, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lv[y] = lvl
        if keymode == 'fixed':
            y0 = FIXEDW[gname]; seen = {y0}; orbs = []
            for y in sorted(lv):
                if y in seen: continue
                orb = {y}; st = [y]
                while st:
                    x = st.pop()
                    for g in hg:
                        z = ap(g, x, m)
                        if z not in orb: orb.add(z); st.append(z)
                seen |= orb
                if all(x in lv for x in orb): orbs.append(orb)
            orbs.sort(key=lambda o: (max(lv[x] for x in o), -len(o)))
            keyw = [y0]
            for o in orbs:
                for x in sorted(o, key=lambda x: (lv[x], x)):
                    if len(keyw) < r: keyw.append(x)
        else:
            seen = set(); orbs = []
            for y in sorted(lv):
                if y in seen: continue
                orb = {y}; st = [y]
                while st:
                    x = st.pop()
                    for g in hg:
                        z = ap(g, x, m)
                        if z not in orb: orb.add(z); st.append(z)
                seen |= orb
                if w[0] not in orb and all(x in lv for x in orb) and len(orb) >= r: orbs.append(orb)
            orbs.sort(key=lambda o: (-min(lv[x] for x in o), -len(o)))
            keyw = sorted(orbs[0], key=lambda x: (lv[x], x))[:r]
        ib = rebase(keyw[0], gname, r)
        if only and gname not in only: continue
        prep3(hg, m, ib, hf, w, r, G=H, verbose=False, key=keyw)
        make_ltsb([tuple(g) for g in H], m, ib, hf, hf + '.ltsb')
        lh = {'LTSHFILE': hf}; lb = {'LTSHFILE': hf, 'LTSBFILE': hf + '.ltsb'}
        o0, _ = run('proto', ib, lh); ob, _ = run('proto', ib, lb)
        o11, _ = run('rc11', ib, lb); o5, _ = run('b5', ib, lb)
        oc, ec = run('rc11', ib, dict(lb, LWE11CHECK='1')); on, _ = run('rc11', ib, lh)
        reps = reps_of(o11)
        lbp = [l for l in ob.split('\n') if l.startswith('LBPRUNE')]
        lbn = sum(int(x.split(':')[1]) for x in lbp[0].split()[1:]) if lbp else -1
        nc, outside, eq = closure_check(reps, hg)
        same = (core(o11) == core(ob), core(o5) == core(ob), core(oc) == core(ob), core(on) == core(o0))
        chk = ('LWE11CHECK passed' in ec) and ('LB check' in ec)
        ok = all(same) and chk and eq and outside == 0 and nc == len(solf)
        allok &= ok
        tag = f"{gname}_r{r}".replace('(', '').replace(')', '').replace('@', '_')
        for nm, out in (('proto0', o0), ('protob', ob), ('rc11', o11), ('b5', o5), ('rc11chk', oc), ('rc11nolb', on)):
            open(f'{ALG}/logs/qr48lb/{keymode}_{tag}_{nm}.log', 'w').write(out)
        open(f'{ALG}/logs/qr48lb/{keymode}_{tag}_rc11chk.err', 'w').write(ec)
        print(f"group {gname} |H|={len(H)} r={r} key levels {[lv[x] for x in keyw]}: reps {len(reps)} (without LTSB "
              f"{len(reps_of(o0))}, LTSB prunes {lbn}), H-closure {nc}, outside {outside}, equals plain set {eq}; "
              f"rc11=proto {same[0]}, lwe11b5=proto {same[1]}, rc11 CHECK=proto {same[2]} [{ec.strip().splitlines()[0] if ec.strip() else ''}], "
              f"rc11 without LTSB = proto without {same[3]} -> {'OK' if ok else 'FAIL'} ({time.time() - t0:.0f} s)", flush=True)
print(f"ALL {'OK' if allok else 'FAIL'}", flush=True)
