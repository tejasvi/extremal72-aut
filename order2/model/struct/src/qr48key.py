"""Hybrid LTS-r (lwe8 + symprep3) validation on QR48.  For several groups H <= Aut(Y48) (full group, point
stabiliser, random 2-generated, random cyclic) and r in {1,2,3}: the H-orbit closure (generator BFS,
gauge-normalised) of the reported representatives must equal exactly the plain solution set; for small H the
explicit engine (lwe7 + symprep2) must report the identical representative set.  Optional argv[1] = 'relaxed':
keep only the weight-6 constraints (a different, larger solution set).  argv[2] = flag variant 'qr' or 'alt'."""
import sys, pickle, subprocess, os, random
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from common import *
import mkinst
from qrctl import setup
from nautyaut import aut_gens
from symprep import closure, ap, coords_fn
from symprep2 import prep2
from symprep3 import prep3
env = dict(os.environ, TMPDIR='<HOME>/c72/c2opt/struct/tmp')
mode = sys.argv[1] if len(sys.argv) > 1 else 'full'
flagname = sys.argv[2] if len(sys.argv) > 2 else 'qr'
keymode = sys.argv[3] if len(sys.argv) > 3 else 'prefix'
S = setup(47); m = 24; d = 12
Yg = S['Ygens']
gens = aut_gens(Yg, m)
G = closure(gens, m)
D = pickle.load(open('<HOME>/c72/c2opt/struct/inst/qr48.pkl', 'rb'))
w = D['L']['w']
if flagname == 'alt': w = w[1:4][::-1] + [w[0]] + w[4:]
L = mkinst.build(Yg, w, m=m, d=d, verbose=False)
if mode == 'relaxed':
    keep = [k for k, c in enumerate(L['cons']) if c[1] == 6]
    L['cons'] = [L['cons'][k] for k in keep]; L['meta'] = [L['meta'][k] for k in keep]
inst = f'<HOME>/c72/c2opt/struct/inst/qr48k_{mode}_{flagname}_{keymode}.txt'
mkinst.export(L, inst)
def run(eng, extra):
    out = subprocess.run([f'<HOME>/c72/c2opt/struct/src/{eng}', inst], capture_output=True, text=True, env=dict(env, **extra)).stdout
    return [int(l.split()[1], 16) for l in out.split('\n') if l.startswith('SOLUTION')], [l for l in out.split('\n') if l.startswith('DONE')]
plain, dn = run(os.environ.get('ENG', 'lwe10'), {})
solf = set(plain)
print(f"mode {mode} flag {flagname}: |Aut(Y48)| = {len(G)}, plain solutions {len(solf)} ({dn[0] if dn else ''})", flush=True)
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
rng = random.Random(11)
def gen_subgroup(elems):
    es = set(map(tuple, elems)); hg = []
    while True:
        hg.append(list(rng.choice(elems)))
        if len(closure(hg, m)) == len(es): return hg
pstab = [g for g in G if g[0] == 0]
FIXEDW = {}
groups = [('Aut', gens, G), ('PointStab', gen_subgroup(pstab), pstab)]
if keymode == 'fixed':
    # H = Stab_G(y) for a low word y at a late level (y is H-fixed: orbit size 1, S0 = H)
    lvq = {}
    for (lvl, wt_, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lvq[y] = lvl
    ys = sorted(lvq, key=lambda y: (-lvq[y], y))
    groups = []
    for y in (ys[5], ys[60], ys[200]):
        H = [g for g in G if ap(g, y, m) == y]
        groups.append((f'Stab(y@lv{lvq[y]})', gen_subgroup(H), H))
        FIXEDW[f'Stab(y@lv{lvq[y]})'] = y
if keymode != 'fixed':
    r2 = [list(rng.choice(G)) for _ in range(2)]; groups.append(('Rand2', r2, closure(r2, m)))
    r1 = [list(rng.choice(G))]; groups.append(('Rand1', r1, closure(r1, m)))
for gname, hg, H in groups:
    for r in ((1, 2, 3, 6) if keymode in ('orbit', 'fixed') else (1, 2, 3)):
        hf = inst + f'.{gname}.r{r}.ltsh'
        if keymode == 'fixed':
            # key: the H-fixed word first, then words of the earliest-complete other H-orbits (by max level)
            lv = {}
            for (lvl, wt_, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lv[y] = lvl
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
            print(f"   fixed key: |H|={len(H)} key levels {[lv[x] for x in keyw]}", flush=True)
            prep3(hg, m, inst, hf, w, r, G=H, verbose=False, key=keyw)
        elif keymode == 'orbit':
            # key words: r words of ONE H-orbit of low words not containing w0, sorted by constraint level;
            # orbit chosen with the largest minimum level (first key word as late as possible)
            lv = {}
            for (lvl, wt, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lv[y] = lvl
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
            print(f"   orbit key: |O|={len(orbs[0])} key levels {[lv[x] for x in keyw]}", flush=True)
            prep3(hg, m, inst, hf, w, r, G=H, verbose=False, key=keyw)
        elif keymode == 'late':
            # key words: low words whose constraints sit at later levels, in a scrambled order
            lv = {}
            for (lvl, wt, forms, bad), (y, ub) in zip(L['cons'], L['meta']): lv[y] = lvl
            cands = sorted(lv, key=lambda y: (-lv[y], y))
            keyw = [cands[3], cands[40], cands[7]][:r]
            prep3(hg, m, inst, hf, w, r, G=H, verbose=False, key=keyw)
        else:
            prep3(hg, m, inst, hf, w, r, G=H, verbose=False)
        reps, dn = run(os.environ.get('ENG', 'lwe10'), {'LTSHFILE': hf})
        nc, outside, eq = closure_check(reps, hg)
        extra = ''
        if len(H) <= 6000 and keymode == 'prefix':
            lf = inst + f'.{gname}.r{r}.ltsr'
            prep2(hg, m, inst, lf, w, r, verbose=False, G=H)
            reps7, _ = run('lwe7', {'LTSFILE': lf})
            extra = f"; explicit engine identical reps: {set(reps7) == set(reps)}"
        print(f"group {gname} |H|={len(H)} r={r}: reps {len(reps)}, H-closure {nc}, outside {outside}, equals plain set: {eq}{extra}", flush=True)
