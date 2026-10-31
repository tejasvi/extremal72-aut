"""Independent per-code coverage checker for the C2 split runs (audit, written from scratch).

usage: cov_c2.py --pkg PKGDIR --parts DIR [--npart N] [--split S] [--fleet RESULTDIR]
                 [--engines SHA,SHA,...] [--prefix FILE] [--origin FILE] [--report OUT]

Checks
 1. Package: PLAN.txt (SPLIT_LEVEL, NPART), INPUTS.sha256 (package files relative to PKGDIR, frozen/ files relative
    to PKGDIR/..), instance structure (N, NLEV, k_t and constraint count per level) from inst.txt.
 2. Parts: exactly p0..p{NPART-1}.log; every log has exactly one DONE line with the right split/part/NPART/N and
    nsol 0, no STOPPED line, no SOLUTION line, exactly the NLEV LEVEL lines with the instance's k_t and ncons, the
    closing SYMPRUNE line, no unknown line; nodes[t+1] == kids[t] for every t; the prefix (levels <= split) is
    identical in every part (nodes; kids/prunes below the split; prunes at the split).
 3. Prefix reference (optional): LEVEL lines of an independent run of the reference engine over the prefix only
    (NPART huge, PART 0) must reproduce the prefix of the production logs.
 4. Fleet metadata (optional): SHA256SUMS of the logs, ORIGIN.tsv / ENGINES.txt one row per part, engine binary
    in the allowed set, a passing check log for every (box, engine) used.
 5. Totals: per-level disjoint sums below the split, CPU seconds, manifests (sha256 of sorted per-part sha256).
"""
import sys, os, re, hashlib, argparse, glob, json

ap = argparse.ArgumentParser()
ap.add_argument('--pkg', required=True); ap.add_argument('--parts', required=True)
ap.add_argument('--npart', type=int); ap.add_argument('--split', type=int)
ap.add_argument('--fleet'); ap.add_argument('--engines', default='')
ap.add_argument('--prefix'); ap.add_argument('--origin'); ap.add_argument('--report')
ap.add_argument('--inputs-base', default=None, help='base dir for frozen/ entries (default PKGDIR/..)')
ap.add_argument('--inputs-root', default=None, help='base dir for ALL INPUTS.sha256 entries (old runs)')
ap.add_argument('--inputs-file', default=None)
ap.add_argument('--inst', default=None)
ap.add_argument('--alt', action='append', default=[], help='other part dirs: duplicates must be identical or incomplete')
ap.add_argument('--allow-sym', action='store_true', help='SYMFILE (LTS-1) pruning is part of this run (Y39)')
ap.add_argument('--xcheck', default=None, help='directory of reference-engine reruns pN.log (+ SELECTION.txt) for a non-fleet run')
ap.add_argument('--allow-lts', action='store_true', help='LTSFILE (LTS-r) pruning is part of this run')
a = ap.parse_args()

problems = []; notes = []
def P(msg): problems.append(msg)
def sha(fn):
    h = hashlib.sha256()
    with open(fn, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): h.update(b)
    return h.hexdigest()

pkg = a.pkg.rstrip('/')
# ---- 1. package
plan = {}
if os.path.exists(os.path.join(pkg, 'PLAN.txt')):
    for line in open(os.path.join(pkg, 'PLAN.txt')):
        f = line.split()
        if len(f) >= 2 and f[0] in ('SPLIT_LEVEL', 'NPART'): plan[f[0]] = int(f[1])
        if len(f) >= 2 and f[0] == 'LTSBFILE': plan['LTSBFILE'] = f[1]   # rc11 convention: LTSB is a fixed package property
SPL = a.split if a.split is not None else plan.get('SPLIT_LEVEL')
NPART = a.npart if a.npart is not None else plan.get('NPART')
if SPL is None or NPART is None: print('cannot determine SPLIT_LEVEL/NPART'); sys.exit(2)
inp_ok = 0; inp_bad = []
ipath = a.inputs_file or os.path.join(pkg, 'INPUTS.sha256')
if os.path.exists(ipath):
    base_frozen = a.inputs_base or os.path.dirname(os.path.abspath(pkg))
    for line in open(ipath):
        f = line.split()
        if len(f) != 2: continue
        h, name = f
        fn = os.path.join(a.inputs_root, name) if a.inputs_root else (os.path.join(base_frozen, name) if name.startswith('frozen') else os.path.join(pkg, name))
        if not os.path.exists(fn) or sha(fn) != h: inp_bad.append(name)
        else: inp_ok += 1
    if inp_bad: P(f'INPUTS.sha256 mismatch: {inp_bad}')
else:
    P('no INPUTS.sha256')
inst = a.inst or os.path.join(pkg, 'inst.txt')
with open(inst) as f:
    toks = f.read().split()
it = iter(toks)
N, NLEV, NC = int(next(it)), int(next(it)), int(next(it))
vstart = [int(next(it)) for _ in range(NLEV + 1)]
kt = [vstart[t + 1] - vstart[t] for t in range(NLEV)]
ncons = [0] * NLEV
for c in range(NC):
    lv, wt, m, nbad = int(next(it)), int(next(it)), int(next(it)), int(next(it))
    for _ in range(m): next(it); next(it)
    for _ in range(nbad): next(it)
    if 0 <= lv < NLEV: ncons[lv] += 1
    else: P(f'constraint {c} with level {lv} outside 0..{NLEV-1}')
try:
    next(it); P('trailing tokens in inst.txt')
except StopIteration:
    pass

# ---- 2. parts
re_done = re.compile(r'^DONE lwe nsol (\d+) time (\d+)s split (-?\d+) part (\d+)/(\d+) N (\d+)$')
re_lev = re.compile(r'^LEVEL (\d+) kt (\d+) ncons (\d+) nodes (\d+) kids (\d+) symprune (\d+)(?: ltsprune (\d+) lhprune (\d+))?$')
re_end = re.compile(r'^SYMPRUNE at leaves (\d+)(?: LTSPRUNE at leaves (\d+) LHPRUNE at leaves (\d+))?$')
re_lb = re.compile(r'^LBPRUNE((?: \d+:\d+)+)$')   # rc11 / lwe10b with LTSBFILE: bit-granular prunes per level (included in lhprune)
pdir = a.parts.rstrip('/')
present = {}
for fn in os.listdir(pdir):
    m = re.match(r'^p(\d+)\.log$', fn)
    if m: present[int(m.group(1))] = os.path.join(pdir, fn)
    elif not fn.endswith('.tmp'): notes.append(f'extra file in parts dir: {fn}')
tmpfiles = [fn for fn in os.listdir(pdir) if fn.endswith('.tmp')]
if tmpfiles: notes.append(f'{len(tmpfiles)} .tmp files in parts dir (in-flight or abandoned)')
missing = [p for p in range(NPART) if p not in present]
extra = sorted(p for p in present if p >= NPART)
if missing: P(f'missing parts: {len(missing)} e.g. {missing[:10]}')
if extra: P(f'part ids >= NPART present: {extra[:10]}')
prefix_ref = None; nsol_total = 0; tsum = 0; nsolution_lines = 0; nstopped = 0
lev_sum = [[0] * 5 for _ in range(NLEV)]; bad_parts = {}; part_sha = {}
xsym = xlts = 0; xsym_parts = set(); xlts_parts = set()   # SYMFILE / LTSFILE prunes (levels and leaves)
lb_parts = 0; lb_total = 0   # parts with an LBPRUNE line (bit-granular LTS), and their LB prunes
# rc14g's stderr build banner: the exact line of the package's own build (fprintf in frozen_rc14g/<pkg>/lwe11.c), nothing else
RC14G_BANNER = {'y40': 'lwe11: generated lane loops for levels 8 9 10', 'y12-lb2': 'lwe11: generated lane loops for levels 8 9 10',
                'y15-lb': 'lwe11: generated lane loops for levels 7 8'}
pkg_banner = RC14G_BANNER.get(os.path.basename(a.pkg.rstrip('/'))); banner_parts = set()
for p in sorted(present):
    if p >= NPART: continue
    fn = present[p]
    raw = open(fn, 'rb').read(); part_sha[p] = hashlib.sha256(raw).hexdigest()
    lines = raw.decode('utf-8', 'replace').splitlines()
    dones = []; levs = {}; ends = 0; errs = []; lbl = None; lhleaf = 0
    for ln in lines:
        if not ln.strip(): continue
        m = re_done.match(ln)
        if m: dones.append(m); continue
        m = re_lev.match(ln)
        if m:
            t = int(m.group(1))
            if t in levs: errs.append(f'duplicate LEVEL {t}')
            levs[t] = [int(m.group(i) or 0) for i in range(2, 9)]; continue
        m = re_lb.match(ln)
        if m:
            if lbl is not None: errs.append('two LBPRUNE lines')
            lbl = {int(a): int(b) for a, b in (x.split(':') for x in m.group(1).split())}
            continue
        m = re_end.match(ln)
        if m:
            ends += 1; e1, e2 = int(m.group(1)), int(m.group(2) or 0); lhleaf = int(m.group(3) or 0)
            xsym += e1; xlts += e2
            if e1: xsym_parts.add(p)
            if e2: xlts_parts.add(p)
            continue
        if 'STOPPED' in ln: nstopped += 1; errs.append('STOPPED line'); continue
        if ln.startswith('SOLUTION'): nsolution_lines += 1; errs.append('SOLUTION line'); continue
        if pkg_banner is not None and ln == pkg_banner: banner_parts.add(p); continue   # checked against ENGINES.txt below
        errs.append(f'unknown line: {ln[:80]}')
    if len(dones) != 1: errs.append(f'{len(dones)} DONE lines')
    else:
        d = dones[0]
        nsol, tm, spl, part, npart, nn = map(int, d.groups())
        nsol_total += nsol; tsum += tm
        if nsol: errs.append(f'nsol {nsol}')
        if spl != SPL or part != p or npart != NPART or nn != N: errs.append(f'DONE fields split {spl} part {part}/{npart} N {nn}')
    if ends != 1: errs.append(f'{ends} closing SYMPRUNE lines')
    if sorted(levs) != list(range(NLEV)): errs.append(f'LEVEL set {sorted(levs)[:3]}..')
    else:
        for t in range(NLEV):
            k, nc, nodes, kids, sp, lp, hp = levs[t]
            xsym += sp; xlts += lp
            if sp: xsym_parts.add(p)
            if lp: xlts_parts.add(p)
            if k != kt[t] or nc != ncons[t]: errs.append(f'level {t} kt/ncons {k}/{nc} != instance {kt[t]}/{ncons[t]}')
            if t + 1 < NLEV and levs[t + 1][2] != kids: errs.append(f'nodes[{t+1}] {levs[t+1][2]} != kids[{t}] {kids}')
        # bit-granular LTS: LB prunes per level are part of lhprune (lwe10b / rc11 counting)
        if lbl is not None:
            lb_parts += 1; lb_total += sum(lbl.values())
            if sorted(lbl) != list(range(NLEV + 1)): errs.append('LBPRUNE levels incomplete')
            elif any(lbl[t] > levs[t][6] for t in range(NLEV)) or lbl[NLEV] > lhleaf: errs.append('lbprune > lhprune')
        # prefix signature: nodes for t <= SPL; kids and prunes for t < SPL; prunes at SPL; LB prunes at t <= SPL
        sig = tuple([levs[t][2] for t in range(SPL + 1)] + [tuple(levs[t][3:]) for t in range(SPL)] + [tuple(levs[SPL][4:])]
                    + [tuple(lbl[t] for t in range(SPL + 1)) if lbl is not None and sorted(lbl) == list(range(NLEV + 1)) else None])
        if prefix_ref is None: prefix_ref = (sig, p)
        elif sig != prefix_ref[0]: errs.append(f'prefix differs from part {prefix_ref[1]}')
        for t in range(NLEV):
            if t > SPL:
                for i in range(5): lev_sum[t][i] += levs[t][2 + i]
            elif t == SPL:
                lev_sum[t][1] += levs[t][3]   # kids of the explored level-SPL nodes are disjoint
    if errs: bad_parts[p] = errs
if bad_parts:
    P(f'{len(bad_parts)} bad parts, e.g. ' + '; '.join(f'p{p}: {e[:3]}' for p, e in list(bad_parts.items())[:5]))
# ---- 3. prefix reference
if a.prefix:
    ref = {}; reflb = None
    for ln in open(a.prefix):
        m = re_lev.match(ln.strip())
        if m: ref[int(m.group(1))] = [int(m.group(i) or 0) for i in range(2, 9)]
        m = re_lb.match(ln.strip())
        if m: reflb = {int(x): int(y) for x, y in (z.split(':') for z in m.group(1).split())}
    if prefix_ref is None or len(ref) < SPL + 1: P('prefix reference unusable')
    else:
        rsig = tuple([ref[t][2] for t in range(SPL + 1)] + [tuple(ref[t][3:]) for t in range(SPL)] + [tuple(ref[SPL][4:])]
                     + [tuple(reflb[t] for t in range(SPL + 1)) if reflb is not None else None])
        if rsig != prefix_ref[0]: P(f'prefix reference differs from the production prefix: ref {rsig[:SPL+1]} prod {prefix_ref[0][:SPL+1]}')
        else: notes.append('prefix reproduced by an independent reference run (nodes, kids, prunes at levels <= split)')
PINNED_LWE10B = {'7766661c5c1ff70be51a9ac7b76e983b68241540b62b8f871b3935edde347893',    # frozen_rc13 / frozen_rc14 lwe10b
                 '246ceb0bbe72f7f18c541de59f5622cd75b0d2c19196e55fa1def17783ca77e1'}    # frozen_b7 lwe10b

def xcheck_compare(xd, pkgname, prod_mtype=None):
    """reference-engine reruns xd/pN.log (lwe8 on seeded parts) must equal the production logs; split reruns
    xd/split/pN/sJ.log must add up to them (xsplit_agg.py rule). prod_mtype: part -> production machine type"""
    seeded = []; i = 0
    while len(seeded) < 8 and i < 100000:
        k = int(hashlib.sha256(f'c2-xcheck-{pkgname}-{i}'.encode()).hexdigest(), 16) % NPART; i += 1
        if k not in seeded: seeded.append(k)
    listed = []
    sp = os.path.join(xd, 'SELECTION.txt')
    if os.path.exists(sp):
        for line in open(sp):
            if line.startswith('#') or not line.strip(): continue
            listed = [int(x) for x in line.split()]
    if listed and listed != seeded:
        notes.append(f'xcheck SELECTION {listed} differs from the seeded rule {seeded} (external parts skipped?)')
    def norm(fn):
        L = open(fn, errors='replace').read().splitlines()
        return [re.sub(r' time \d+s', '', x) for x in L if x.startswith(('DONE', 'LEVEL', 'SYMPRUNE', 'LBPRUNE', 'SOLUTION'))], \
               any('STOPPED' in x for x in L), sum(1 for x in L if x.startswith('DONE'))
    xs = same = diff = inc = 0; xdiff = []; state = {}; copies = []
    for fn in sorted(os.listdir(xd)):
        # pN.log, plus pN.<box>.log for a later copy of the same rerun (fleet hedge, 10-27): every copy must equal production
        m = re.match(r'^p(\d+)(?:\.(hpc-[A-Za-z0-9-]+))?\.log$', fn)
        if not m: continue
        q = int(m.group(1)); xs += 1
        if m.group(2): copies.append(fn)
        if listed and q not in listed: notes.append(f'xcheck p{q} not in SELECTION.txt')
        a_, st, nd = norm(os.path.join(xd, fn))
        if st or nd != 1: inc += 1; state.setdefault(q, []).append('incomplete'); continue
        if q not in present: diff += 1; xdiff.append(q); state.setdefault(q, []).append('differ'); continue
        b_, _, _ = norm(present[q])
        if a_ == b_: same += 1; state.setdefault(q, []).append('identical')
        else: diff += 1; xdiff.append(q); state.setdefault(q, []).append('differ')
    notes.append(f'xcheck (reference-engine reruns): {xs} logs of {len(listed) or 8} selected; identical {same}, '
                 f'incomplete {inc}, DIFFERENT {diff} {xdiff[:8]}')
    if copies: notes.append(f'xcheck later copies of a rerun (pN.<box>.log), each compared with production: {len(copies)} {copies[:4]}')
    if diff: P(f'xcheck: {diff} reference-engine reruns differ from production: {xdiff[:8]}')
    # split reruns (fleet XSPLIT, reviewed 10-25): sub-parts (SPL, N*NPART, p + j*NPART) of the pinned lwe10b, each log
    # listed in xd/SHA256SUMS and in xd/ORIGIN.tsv (exe pinned, env not BAD, CPU generation other than the production's)
    sd = os.path.join(xd, 'split')
    if not os.path.isdir(sd): return
    import importlib.util
    spec = importlib.util.spec_from_file_location('xsplit_agg', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'xsplit_agg.py'))
    xa = importlib.util.module_from_spec(spec); spec.loader.exec_module(xa)
    xsums = {}; orow = {}
    if os.path.exists(os.path.join(xd, 'SHA256SUMS')):
        for line in open(os.path.join(xd, 'SHA256SUMS')):
            w = line.split()
            if len(w) == 2: xsums[w[1]] = w[0]
    if os.path.exists(os.path.join(xd, 'ORIGIN.tsv')):
        for line in open(os.path.join(xd, 'ORIGIN.tsv')):
            f = line.rstrip('\n').split('\t')
            if f[0].startswith('split/'): orow.setdefault(re.sub(r'\.log$', '', f[0]), []).append(f)
    GEN = {'famD': 3, 'famE': 3, 'famC': 4, 'famA': 5, 'famB': 5}
    gen = lambda mt: GEN.get((mt or '').split('-')[0])
    cnt = {'identical': 0, 'incomplete': 0, 'differ': 0, 'records': 0}; sdiff = []; srec = []
    for dn in sorted(os.listdir(sd)):
        m = re.match(r'^p(\d+)$', dn)
        if not m: continue
        q = int(m.group(1)); pd = os.path.join(sd, dn)
        if listed and q not in listed: notes.append(f'xcheck split p{q} not in SELECTION.txt')
        subs = sorted((f for f in os.listdir(pd) if re.match(r'^s\d+\.log$', f)), key=lambda f: int(f[1:-4]))
        done = [xa.parse(os.path.join(pd, f)) for f in subs]
        if not subs or any(x['stopped'] or x['ndone'] != 1 or not x['d'] for x in done): st = 'incomplete'
        elif len(set(x['d'][3] for x in done)) != 1 or done[0]['d'][3] % NPART: st = 'differ'
        elif len(subs) < done[0]['d'][3] // NPART: st = 'incomplete'
        elif q not in present or xa.problems(present[q], NPART, [os.path.join(pd, f) for f in subs], banner=pkg_banner): st = 'differ'
        else:
            rec = []
            for f in subs:
                rel = f'split/{dn}/{f}'
                if xsums.get(rel) != sha(os.path.join(pd, f)): rec.append(f'{rel} sha not listed or different')
                o = orow.get(rel[:-4], [])
                ex = [c[4:] for r in o for c in r if c.startswith('exe:')]; ev = [c for r in o for c in r if c.startswith('env:')]
                if len(o) != 1 or len(ex) != 1 or ex[0] not in PINNED_LWE10B: rec.append(f'{rel} ORIGIN row/exe {ex[:1]}')
                elif not ev or ev[0].startswith('env:BAD') or ev[0] == 'env:-': rec.append(f'{rel} env {ev[:1]}')
                elif prod_mtype is not None and (gen(o[0][2]) is None or gen(o[0][2]) == gen(prod_mtype.get(q))):
                    rec.append(f'{rel} on {o[0][2]}, production on {prod_mtype.get(q)}: same or unknown CPU generation')
            st = 'records' if rec else 'identical'
            srec += rec
        cnt[st] += 1; state.setdefault(q, []).append(st)
        if st == 'differ': sdiff.append(q)
    good = sum(1 for q in (listed or state) if state.get(q) and 'identical' in state[q] and not set(state[q]) & {'differ', 'records'})
    notes.append(f'xcheck split reruns: {sum(cnt.values())} parts; identical {cnt["identical"]}, incomplete {cnt["incomplete"]}, '
                 f'DIFFERENT {cnt["differ"]} {sdiff[:8]}, record problems {cnt["records"]} {srec[:3]}; selected parts with an '
                 f'identical cross-check (single or split; both identical where both exist): {good} of {len(listed) or 8}')
    if cnt['differ']: P(f'xcheck: {cnt["differ"]} split reruns do not add up to production: {sdiff[:8]}')
    if cnt['records']: P(f'xcheck: split rerun records incomplete or wrong: {srec[:3]}')

# ---- 4. fleet metadata
allowed = set(x for x in a.engines.split(',') if x)
if a.fleet:
    fr = a.fleet.rstrip('/')
    sums = {}
    for line in open(os.path.join(fr, 'SHA256SUMS')):
        h, name = line.split(); sums[os.path.basename(name)] = h
    sha_bad = [p for p in part_sha if sums.get(f'p{p}.log') != part_sha[p]]
    if sha_bad: P(f'SHA256SUMS mismatch for {len(sha_bad)} parts, e.g. {sha_bad[:5]}')
    if len(sums) != NPART: P(f'SHA256SUMS has {len(sums)} entries, NPART {NPART}')
    eng = {}; exe = {}; envt = {}
    for line in open(os.path.join(fr, 'ENGINES.txt')):
        f = line.split('\t') if '\t' in line else line.split()
        if len(f) < 4: continue
        name = os.path.basename(f[0]); eng.setdefault(name, []).append((f[1], f[2], f[3].strip()))
        exe[name] = f[4].strip() if len(f) > 4 else None   # fleet from 10-21 17:38 UTC: measured /proc/PID/exe sha
        envt[name] = f[5].strip() if len(f) > 5 else None  # fleet from ~17:55 UTC: env:clean | env:noswitch(N) | env:- | env:BAD:...
    origin = {}
    for line in open(os.path.join(fr, 'ORIGIN.tsv')):
        f = line.rstrip('\n').split('\t')
        if len(f) < 5: continue
        origin.setdefault(f[0], []).append(f)
    eng_bad = []; boxes = set()
    for p in range(NPART):
        e = eng.get(f'p{p}.log', [])
        o = origin.get(f'p{p}', [])
        if len(e) != 1 or len(o) != 1: eng_bad.append((p, len(e), len(o))); continue
        ename, bsha, box = e[0]
        if allowed and bsha not in allowed: eng_bad.append((p, 'binary', bsha[:12]))
        if o[0][4] != part_sha.get(p): eng_bad.append((p, 'origin sha'))
        if o[0][1] != box or o[0][3] != ename: eng_bad.append((p, 'origin/engines disagree'))
        boxes.add((box, ename, bsha))
    if eng_bad: P(f'ENGINES/ORIGIN problems for {len(eng_bad)} parts, e.g. {eng_bad[:5]}')
    # measured executable sha (5th column 'exe:<sha>' or 'exe:-'): must equal the configured sha when present
    xm = xu = xn = 0; xbad = []
    for p in range(NPART):
        e = eng.get(f'p{p}.log', []); x = exe.get(f'p{p}.log')
        if len(e) != 1: continue
        if x is None: xn += 1
        elif x == 'exe:-': xu += 1
        elif x.startswith('exe:') and x[4:] == e[0][1]: xm += 1
        else: xbad.append((p, x[:16]))
    notes.append(f'measured exe sha: equal to configured {xm}, not measured (exe:-) {xu}, no column (before 17:38 UTC) {xn}, MISMATCH {len(xbad)}')
    if xbad: P(f'measured executable sha differs from the configured engine sha for {len(xbad)} parts, e.g. {xbad[:5]}')
    # measured engine environment (6th column): env:BAD fails; clean / noswitch / unmeasured are counted
    ec = {'clean': 0, 'noswitch': 0, 'unmeasured': 0, 'nocol': 0}; ebad = []
    for p in range(NPART):
        t = envt.get(f'p{p}.log')
        if t is None: ec['nocol'] += 1
        elif t == 'env:clean': ec['clean'] += 1
        elif re.match(r'^env:noswitch\(\d+\)$', t): ec['noswitch'] += 1
        elif t == 'env:-': ec['unmeasured'] += 1
        else: ebad.append((p, t[:40]))
    notes.append(f"measured engine environment: clean {ec['clean']}, no switch {ec['noswitch']}, not measured {ec['unmeasured']}, no column {ec['nocol']}, BAD/unknown {len(ebad)}")
    ebad_parts = ebad   # decided after the second runs are read (a clean identical gated second run counts instead)
    # rc14g prints one stderr banner per run (frozen_rc14g/<pkg>/lwe11.c); it must appear exactly in the parts run by rc14g
    g_parts = {int(n[1:-4]) for n, lst in eng.items() if len(lst) == 1 and lst[0][0].startswith('rc14g') and n[1:-4].isdigit()}
    if banner_parts or g_parts:
        notes.append(f'rc14g build banner ("lwe11: generated lane loops for levels ...") in {len(banner_parts)} parts; parts run by rc14g: {len(g_parts)}')
        if banner_parts != g_parts: P(f'rc14g banner and ENGINES.txt disagree on {len(banner_parts ^ g_parts)} parts, e.g. {sorted(banner_parts ^ g_parts)[:5]}')
    # every (box, engine) used needs a passing check log (binary, inputs, frozen sources, probe); the lwe8 identity
    # step ("full" check) is required at least once per (machine family, engine) used, as the project's policy allows
    # "light" checks on the other boxes of a family. Family from ENGINES_CHECKS.txt, else the log's cpu string.
    fam = {}
    ecp = os.path.join(fr, 'ENGINES_CHECKS.txt')
    if os.path.exists(ecp):
        for line in open(ecp):
            f = line.split()
            if len(f) >= 5 and not line.startswith('#'): fam[(f[3], f[1])] = f[0]
    def famof(box, ename, txt):
        if (box, ename) in fam: return fam[(box, ename)]
        m = re.search(r' cpu (.+)', txt.splitlines()[0] if txt else '')
        return 'cpu:' + (m.group(1).strip() if m else '?')
    # a check log fails on any negative marker; 'full' = the lwe8 identity step passed (and, for an LTSB package, the
    # lwe10b + LTSBFILE identity step and the INPUTS listing of the LTSB file)
    NEG = ('DIFFER', 'MISMATCH', 'MISSING', 'NOT LISTED', 'FAILED', 'REFUS', 'PRESENT BUT')
    ltsbpkg = 'LTSBFILE' in plan
    def is_full(txt):
        if not re.search(r'LWE8/LWE11\w* IDENTICAL', txt): return False   # rc-line prints LWE11, lwe11b-line LWE11B
        return (not ltsbpkg) or ('IDENTICAL WITH LTSBFILE' in txt and 'LTSBFILE listed in INPUTS.sha256' in txt)
    full_ok = set()
    for fn in glob.glob(os.path.join(fr, 'checks', '*.log')):
        m = re.match(r'^(.+)\.([^.]+)\.log$', os.path.basename(fn))
        if not m: continue
        txt = open(fn).read()
        if all(n in txt for n in ('inputs OK', 'frozen sources OK', 'PROBE OK', 'binary in use: ')) and is_full(txt) \
                and not any(x in txt for x in NEG) and re.search(r'END \S+ rc 0', txt):
            bin_used = re.search(r'binary in use: (\S+)', txt).group(1)
            full_ok.add((famof(m.group(1), m.group(2), txt), m.group(2), bin_used))
    chk_bad = []; nfull = nlight = 0; nolog = []
    for box, ename, bsha in sorted(boxes):
        cands = glob.glob(os.path.join(fr, 'checks', f'{box}.{ename}.log'))
        if not cands: nolog.append((box, ename, bsha)); continue
        txt = open(cands[0]).read()
        need = ['inputs OK', 'frozen sources OK', 'PROBE OK', f'binary in use: {bsha}']
        miss = [n for n in need if n not in txt]
        negs = [x for x in NEG if x in txt]
        if miss or negs or not re.search(r'END \S+ rc 0', txt): chk_bad.append((box, ename, miss + negs)); continue
        if is_full(txt): nfull += 1
        else:
            nlight += 1
            if (famof(box, ename, txt), ename, bsha) not in full_ok:
                chk_bad.append((box, ename, f'light check and no full check for family {famof(box, ename, txt)}'))
    def gated(box, ename):
        cands = glob.glob(os.path.join(fr, 'checks', f'{box}.{ename}.log'))
        if not cands: return False
        txt = open(cands[0]).read()
        m = re.search(r'binary in use: (\S+)', txt)
        if not m or (allowed and m.group(1) not in allowed): return False
        if any(n not in txt for n in ('inputs OK', 'frozen sources OK', 'PROBE OK')) or any(x in txt for x in NEG) \
                or not re.search(r'END \S+ rc 0', txt): return False
        return is_full(txt) or (famof(box, ename, txt), ename, m.group(1)) in full_ok
    notes.append(f'check logs of boxes used: full {nfull}, light {nlight} (full checks per family/engine: '
                 + ', '.join(sorted(set(f'{x[0]}:{x[1]}' for x in full_ok))) + ')')
    # reference-engine cross-checks: results/<pkg>/xcheck/pN.log (lwe8 reruns of seeded parts) must equal production
    xd = os.path.join(fr, 'xcheck')
    if os.path.isdir(xd): xcheck_compare(xd, os.path.basename(fr), {int(k[1:]): v[0][2] for k, v in origin.items() if len(v) == 1 and k[1:].isdigit()})
    # second runs kept by the controller (dups/p<part>.<box>.<time>.log; '.bad.' = rejected logs): each must equal the stored part
    dd = os.path.join(fr, 'dups')
    if os.path.isdir(dd):
        def dnorm(fn):
            return [re.sub(r' time \d+s', '', x) for x in open(fn, errors='replace').read().splitlines()
                    if x.startswith(('DONE', 'LEVEL', 'SYMPRUNE', 'LBPRUNE', 'SOLUTION'))]
        dsame = ddiff = dbad = 0; dlist = []
        for fn in sorted(os.listdir(dd)):
            m = re.match(r'^p(\d+)\.(.+)\.(\d+)\.log$', fn)
            if not m: continue
            if '.bad.' in fn: dbad += 1; continue
            q = int(m.group(1))
            if q not in present: ddiff += 1; dlist.append(q); continue
            if dnorm(os.path.join(dd, fn)) == dnorm(present[q]): dsame += 1
            else: ddiff += 1; dlist.append(q)
        notes.append(f'second runs (dups/): identical to the stored part {dsame}, DIFFERENT {ddiff} {dlist[:8]}, rejected (.bad.) {dbad}')
        if ddiff: P(f'dups: {ddiff} second runs differ from the stored part: {dlist[:8]}')
    rerun = {}
    if nolog or ebad_parts:
        # DUPS.tsv: part, box, machine type, engine, sha, exe:..., env:..., verdict (one row per second run, file in dups/)
        dt = os.path.join(fr, 'DUPS.tsv')
        if os.path.exists(dt) and os.path.isdir(dd):
            for line in open(dt):
                f = line.rstrip('\n').split('\t')
                if len(f) < 4 or not f[0].startswith('p'): continue
                q = int(f[0][1:]); rb, re_ = f[1], f[3]
                dsha = f[4] if len(f) > 4 else ''
                dexe = f[5][4:] if len(f) > 5 and f[5].startswith('exe:') else ''
                denv = f[6] if len(f) > 6 else ''
                # the listed log sha must verify, the log must equal the stored part, the measured exe must be an allowed
                # engine binary, env must not be BAD, and the second box must have a passed check for that engine
                if (allowed and dexe not in allowed) or denv.startswith('env:BAD'): continue
                ok = False
                for fn in glob.glob(os.path.join(dd, f'p{q}.{rb}.*.log')):
                    if '.bad.' not in fn and q in present and sha(fn) == dsha and dnorm(fn) == dnorm(present[q]): ok = True
                if ok and gated(rb, re_): rerun.setdefault(q, []).append((rb, re_))
    if nolog:
        uncovered = []; covered = 0
        for box, ename, bsha in nolog:
            ps = [int(n[1:-4]) for n, lst in eng.items() for e in lst if e[2] == box and e[0] == ename]
            miss = [q for q in ps if q not in rerun]
            covered += len(ps) - len(miss)
            if miss: uncovered.append((box, ename, f'no check log; {len(miss)} of {len(ps)} parts without an identical gated second run'))
        notes.append(f'parts from boxes without any check log: {covered + sum(int(u[2].split(" ")[3]) for u in uncovered)} on {len(nolog)} (box, engine) pairs; '
                     f're-run identically on gated boxes: {covered}')
        chk_bad.extend(uncovered)
    if ebad_parts:
        unc = [x for x in ebad_parts if x[0] not in rerun]
        notes.append(f'parts with env tag BAD/unknown: {len(ebad_parts)}; covered by a clean identical second run on a gated box: '
                     f'{len(ebad_parts) - len(unc)}')
        if unc: P(f'engine environment tag BAD or unknown for {len(unc)} parts without a clean gated second run, e.g. {unc[:5]}')
    if chk_bad: P(f'check logs: {chk_bad}')
    notes.append(f'fleet: {len(boxes)} (box, engine, binary) combinations: ' + ', '.join(f'{b}:{e}:{s[:8]}' for b, e, s in sorted(boxes)))
# a stray SYMFILE/LTSFILE in the environment would add lex-leader tests with foreign data; every such prune is
# counted in the symprune/ltsprune columns (lwe5-lwe11), so zero columns prove that no such test pruned anything
# LTSB is a package property: PLAN 'LTSBFILE name' <=> every part has an LBPRUNE line; the file must be in INPUTS.sha256
nparts_seen = len([p for p in present if p < NPART])
if 'LTSBFILE' in plan:
    if lb_parts != nparts_seen: P(f'PLAN names LTSBFILE but only {lb_parts} of {nparts_seen} parts have an LBPRUNE line')
    lname = plan['LTSBFILE']
    listed = [l.split()[1] for l in open(ipath) if len(l.split()) == 2] if os.path.exists(ipath) else []
    if lname not in listed: P(f'LTSB file {lname} is not listed in INPUTS.sha256')
else:
    if lb_parts: P(f'{lb_parts} parts have an LBPRUNE line but PLAN.txt names no LTSBFILE (mixed or undeclared LTSB use)')
    if os.path.exists(os.path.join(pkg, 'sym.ltsb')): notes.append('sym.ltsb present in the package but PLAN.txt names no LTSBFILE')
if xsym and not a.allow_sym: P(f'SYMFILE (LTS-1) prunes present: {xsym} in {len(xsym_parts)} parts, e.g. {sorted(xsym_parts)[:5]}')
if xlts and not a.allow_lts: P(f'LTSFILE (LTS-r) prunes present: {xlts} in {len(xlts_parts)} parts, e.g. {sorted(xlts_parts)[:5]}')
if a.xcheck and os.path.isdir(a.xcheck): xcheck_compare(a.xcheck, os.path.basename(a.xcheck.rstrip('/')))
if a.origin:   # explore-style ORIGIN list (free text): just report it
    notes.append(f'origin file {a.origin}: {sum(1 for _ in open(a.origin))} lines')
if banner_parts and not a.fleet: P(f'rc14g build banner in {len(banner_parts)} parts without fleet records')
# ---- 5. totals and manifests
tot_below = sum(lev_sum[t][0] for t in range(SPL + 1, NLEV))
digs = sorted(part_sha[p] for p in part_sha)
man1 = hashlib.sha256(''.join(d + '\n' for d in digs).encode()).hexdigest()
lines_sorted = sorted(f'{part_sha[p]}  p{p}.log' for p in part_sha)
man2 = hashlib.sha256(''.join(l + '\n' for l in lines_sorted).encode()).hexdigest()
man3 = hashlib.sha256(''.join(f'{part_sha[p]}  p{p}.log\n' for p in sorted(part_sha)).encode()).hexdigest()
# alternative part dirs: duplicates of a part must be either incomplete (no DONE / STOPPED) or identical in LEVEL lines
def levsig(fn):
    L = [ln for ln in open(fn, errors='replace').read().splitlines() if ln.startswith('LEVEL') or ln.startswith('SYMPRUNE')]
    d = [ln for ln in open(fn, errors='replace').read().splitlines() if ln.startswith('DONE')]
    st = any('STOPPED' in ln for ln in open(fn, errors='replace').read().splitlines())
    dd = re.sub(r' time \d+s', '', d[0]) if len(d) == 1 else None
    return (dd, tuple(L)), st, len(d)
for adir in a.alt:
    same = diff = inc = 0; diffs = []
    for fn in os.listdir(adir):
        m = re.match(r'^p(\d+)\.log$', fn)
        if not m: continue
        q = int(m.group(1))
        if q not in present: continue
        sa, st, nd = levsig(os.path.join(adir, fn))
        if st or nd != 1: inc += 1; continue
        sb, _, _ = levsig(present[q])
        if sa == sb: same += 1
        else: diff += 1; diffs.append(q)
    notes.append(f'alt dir {adir}: duplicates identical {same}, incomplete/stopped {inc}, DIFFERENT {diff} {diffs[:10]}')
    if diff: P(f'alt dir {adir}: {diff} complete duplicates differ from the canonical log')
out = []
out.append(f'package {pkg}: N {N} NLEV {NLEV} NC {NC} split {SPL} NPART {NPART}; INPUTS ok {inp_ok} bad {len(inp_bad)}')
out.append(f'parts present {len([p for p in present if p < NPART])}/{NPART}; bad {len(bad_parts)}; STOPPED lines {nstopped}; SOLUTION lines {nsolution_lines}; nsol sum {nsol_total}')
out.append(f'CPU seconds {tsum} ({tsum/3600:.1f} core-h); nodes below split {tot_below:.6e}')
out.append('per-level disjoint sums below split (nodes, kids, lhprune): ' + '; '.join(f'L{t} {lev_sum[t][0]} {lev_sum[t][1]} {lev_sum[t][4]}' for t in range(SPL + 1, NLEV) if lev_sum[t][0]))
out.append(f'kids at split level (disjoint): {lev_sum[SPL][1]}')
out.append(f'SYMFILE/LTSFILE prunes over all parts, levels and leaves: symprune {xsym} in {len(xsym_parts)} parts; ltsprune {xlts} in {len(xlts_parts)} parts')
out.append(f'bit-granular LTS (LBPRUNE line): {lb_parts} of {len([p for p in present if p < NPART])} parts, LB prunes {lb_total}'
           + (f'; PLAN LTSBFILE {plan["LTSBFILE"]}' if 'LTSBFILE' in plan else '; PLAN without LTSBFILE'))
out.append(f'manifest sha256(sorted digests) {man1}')
out.append(f'manifest sha256(sorted "digest  pN.log" lines) {man2}')
out.append(f'manifest sha256("digest  pN.log" lines in part order) {man3}')
for n in notes: out.append('note: ' + n)
for q in problems: out.append('PROBLEM: ' + q)
out.append('VERDICT ' + ('PASS' if not problems else 'FAIL'))
txt = '\n'.join(out)
print(txt)
if a.report:
    with open(a.report, 'w') as f: f.write(txt + '\n')
