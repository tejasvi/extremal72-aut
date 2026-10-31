"""Provenance checks for a fleet package: (1) parts per engine (label + sha256 from ORIGIN.tsv/ENGINES.txt), written
as ranges to runs2/fleet/<pkg>/PARTS_BY_ENGINE.txt; (2) every (box, engine) pair that produced parts has an ok
check row for that engine in ENGINES_CHECKS.txt, and every (family, engine) pair has at least one ok FULL check
(with the lwe8 identity step; for an LTSB package also the lwe10b+LTSBFILE identity step, the LTSB file listed in
INPUTS.sha256 and its sha256 equal to the package's file).  Usage: fleet_prov.py PKG [PKGDIR]"""
import sys, os, collections, hashlib, re
pkg = sys.argv[1]
PKGDIR = sys.argv[2] if len(sys.argv) > 2 else f'<HOME>/c72/c2opt/struct/runs/{pkg}'
_m = re.search(r'^LTSBFILE (\S+)', open(f'{PKGDIR}/PLAN.txt').read(), re.M)
LTSB = _m.group(1) if _m else None
LTSB_SHA = hashlib.sha256(open(f'{PKGDIR}/{LTSB}', 'rb').read()).hexdigest() if LTSB else None
print(f"LTSB package: {'yes, LTSBFILE ' + LTSB + ' sha256 ' + LTSB_SHA if LTSB else 'no'}")
R = os.environ.get('C2E_TEST_RESULTS', f'<HOME>/c72/fleet/results/{pkg}')   # override only for tests
OUT = os.environ.get('C2E_TEST_OUT', f'<HOME>/c72/explore/runs2/fleet/{pkg}')
origin = [l.rstrip('\n').split('\t') for l in open(f'{R}/ORIGIN.tsv') if l.strip() and not l.startswith('#')]
eng_sha = {}; exe_n = 0; exe_bad = []; env_tags = {}; env_bad = []
for l in open(f'{R}/ENGINES.txt'):
    p = l.split()
    if len(p) >= 3: eng_sha[p[0].split('/')[-1].replace('.log', '')] = (p[1], p[2])
    ev = [x for x in p[4:] if x.startswith('env:')]
    if ev:
        tag = ev[0][4:]; env_tags[tag.split('(')[0] if not tag.startswith('BAD') else 'BAD'] = env_tags.get(tag.split('(')[0] if not tag.startswith('BAD') else 'BAD', 0) + 1
        if tag.startswith('BAD'): env_bad.append(p[0])
    ex = [x for x in p[4:] if x.startswith('exe:')]
    if ex:
        if ex[0] == 'exe:-': exe_na = globals().get('exe_na', 0) + 1; globals()['exe_na'] = exe_na; continue
        exe_n += 1
        if ex[0][4:] != p[2]: exe_bad.append(p[0])
print(f"ENGINES.txt env column (measured engine environment): {env_tags}; BAD rows: {len(env_bad)} {env_bad[:5]}")
print(f"ENGINES.txt exe column (measured /proc exe sha): matching {exe_n - len(exe_bad)}, MISMATCHING {len(exe_bad)} {exe_bad[:5]}, not measured (exe:-) {globals().get('exe_na', 0)}")
by_eng = collections.defaultdict(list); pairs = set(); fam_of = {}
for row in origin:
    part, box, mtype, eng = row[0], row[1], row[2], row[3]
    k = int(part.lstrip('p'))
    lab, sha = eng_sha.get(part, (eng, '?'))
    if lab != eng: print(f"ENGINE LABEL MISMATCH {part}: ORIGIN {eng} ENGINES {lab}")
    by_eng[(lab, sha)].append(k); pairs.add((box, lab))
def ranges(ks):
    ks = sorted(ks); out = []; s = p = ks[0]
    for k in ks[1:]:
        if k == p + 1: p = k
        else: out.append(f'{s}-{p}' if s != p else f'{s}'); s = p = k
    out.append(f'{s}-{p}' if s != p else f'{s}')
    return out
with open(f'{OUT}/PARTS_BY_ENGINE.txt', 'w') as f:
    for (lab, sha), ks in sorted(by_eng.items()):
        f.write(f'# {lab} {sha}: {len(ks)} parts\n' + ' '.join(ranges(ks)) + '\n')
for (lab, sha), ks in sorted(by_eng.items()): print(f"parts on {lab} {sha[:16]}...: {len(ks)}")
# check evidence = the check logs themselves (checks/<box>.<engine>.log); ENGINES_CHECKS.txt is only cross-read
import glob, re
fam_of_box = {}
for row in origin: fam_of_box[row[1]] = row[2].split('-')[0]
logs = {}; other_checks = []; mism = []
for f in glob.glob(f'{R}/checks/*.log'):
    m = re.match(r'^([^.]+)\.([A-Za-z0-9_-]+)\.log$', os.path.basename(f))   # engine labels may contain _ and - (rc14g_y12-lb2)
    if not m: other_checks.append(os.path.basename(f)); continue
    box, eng = m.group(1), m.group(2)
    t = open(f).read()
    sha = (re.search(r'binary in use: ([0-9a-f]{64})', t) or [None, None])[1]
    base = all(x in t for x in ('inputs OK', 'frozen sources OK', 'PROBE OK')) and not any(
        x in t for x in ('MISMATCH', 'DIFFER', 'FAILED', 'NOT LISTED', 'MISSING', 'PRESENT BUT', 'REFUSED'))
    if 'mode fullpar' in t and not re.search(r'^END\b', t, re.M): base = False   # fleet's concurrent full check: log must be complete
    if 'CHECK_BOX' in t and 'CHECK_BOX PASSED' not in t: base = False   # rc13-kit check_box prints a final CHECK_BOX PASSED/FAILED line
    if LTSB:   # the check must have used this package's LTSB file; full = both identity steps
        lsha = (re.search(r'LTSB package, LTSBFILE in use: ([0-9a-f]{64})', t) or [None, None])[1]
        if lsha is not None and lsha != LTSB_SHA: base = False
        if 'not an LTSB package' in t: base = False
        ident = re.search(r'LWE8/LWE11B? IDENTICAL', t) and re.search(r'LWE10B/LWE11B? IDENTICAL WITH LTSBFILE', t) \
            and lsha == LTSB_SHA and 'LTSBFILE listed in INPUTS.sha256' in t
    else:
        ident = 'IDENTICAL' in t
    st = 'full' if base and ident else ('light' if base else 'fail')
    if re.search(r'DIFFER|MISMATCH', t): mism.append((box, eng))   # a real identity/input failure, not a stopped or unfinished check
    logs[(box, eng)] = (st, sha)
eng_sha_of = {}
for (lab, sha), ks in by_eng.items(): eng_sha_of[lab] = sha
bad = []
for (box, eng) in sorted(pairs):
    st, sha = logs.get((box, eng), ('missing', None))
    if st not in ('full', 'light'): bad.append((box, eng, st))
    elif sha != eng_sha_of.get(eng): bad.append((box, eng, f'binary {str(sha)[:12]} != parts {eng_sha_of.get(eng, "?")[:12]}'))
# second runs (fleet DUPS.tsv: part box mtype engine log-sha exe:<measured> env:<tag> identical|DIFFER time; logs in dups/,
# the first log stays in parts/). A part whose first run is on a box without an ok check is covered by a second run that
# is verified here: log file present with that sha, identical to the first log (LEVEL/DONE/SOLUTION/SYMPRUNE/LBPRUNE, time
# stripped), measured exe = the engine's binary, env not BAD, on a box whose own check for that engine is ok (full for LTSB).
def _key(fn):
    return ''.join(re.sub(r'time \d+s', '', l) for l in open(fn) if l.startswith(('LEVEL', 'DONE', 'SOLUTION', 'SYMPRUNE', 'LBPRUNE')))
gated = collections.defaultdict(int); dup_rows = 0; dup_diff = []; dup_unver = []
_gt = [c for c in (l.rstrip('\n').split('\t') for l in open('<HOME>/c72/explore/src/gate_table.tsv') if not l.startswith('#')) if len(c) >= 3]
_sha2name = {c[0]: c[1] for c in _gt}
# admitted binaries for THIS package (project 2026-10-27): gate-table rows passed/conditional, and an rc14g build only in its own package
_admitted = {c[0] for c in _gt if c[2] in ('passed', 'conditional') and (len(c) < 5 or c[4] in ('', pkg))}
if os.path.exists(f'{R}/DUPS.tsv'):
    for l in open(f'{R}/DUPS.tsv'):
        if l.startswith('#') or not l.strip(): continue
        c = l.rstrip('\n').split('\t'); dup_rows += 1
        part, dbox, deng, lsha, dexe, denv, verdict = c[0], c[1], c[3], c[4], c[5], c[6], c[7]
        # fleet (2026-10-23): the measured exe column is authoritative; take the engine name from it via the gate table
        deng = _sha2name.get(dexe[4:20], deng)
        k = int(part.lstrip('p'))
        fl = [f for f in glob.glob(f'{R}/dups/p{k}.{dbox}.*.log') if hashlib.sha256(open(f, 'rb').read()).hexdigest() == lsha]
        same = bool(fl) and _key(fl[0]) == _key(f'{R}/parts/p{k}.log')
        if verdict != 'identical' or (fl and not same): dup_diff.append(part); continue
        # the second box's own check is found by BINARY sha (labels differ between our gate table and fleet's kit names,
        # e.g. rc14g_y12-lb2 vs rc14g_y12); the measured exe must equal the checked binary
        sts = [v[0] for (b, e), v in logs.items() if b == dbox and v[1] == dexe[4:]]
        okbox = ('full' in sts) if LTSB else bool(set(sts) & {'full', 'light'})
        if fl and same and okbox and dexe[4:20] in _admitted and not denv.startswith('env:BAD'): gated[k] += 1
        else: dup_unver.append(part)
# parts whose ENGINES.txt env tag is BAD (or measured exe mismatches) count through a verified gated second run as well
_pk = lambda x: int(re.search(r'p(\d+)\.log', x).group(1))
env_bad_unc = [x for x in env_bad if not gated.get(_pk(x), 0)]
exe_bad_unc = [x for x in exe_bad if not gated.get(_pk(x), 0)]
if env_bad or exe_bad:
    print(f"parts with env BAD or exe mismatch: {len(env_bad)} / {len(exe_bad)}; covered by verified second runs: "
          f"{len(env_bad) - len(env_bad_unc)} / {len(exe_bad) - len(exe_bad_unc)}; uncovered env BAD rows: {len(env_bad_unc)} {env_bad_unc[:5]}; "
          f"uncovered exe MISMATCH rows: {len(exe_bad_unc)} {exe_bad_unc[:5]}")
covered = []
for (box, eng, st) in list(bad):
    ks = [int(r[0].lstrip('p')) for r in origin if r[1] == box and r[3] == eng]
    if ks and all(gated.get(k, 0) for k in ks): covered.append((box, eng, len(ks))); bad.remove((box, eng, st))
if dup_rows:
    print(f"DUPS.tsv second runs: {dup_rows} rows; verified gated identical copies for {sum(1 for v in gated.values() if v)} parts; unverified {len(dup_unver)} {dup_unver[:8]}; "
          + (f"DIFFERENT (second run not identical): {dup_diff[:8]}" if dup_diff else "none different"))
    print(f"production (box, engine) pairs without an ok check whose parts ALL have verified gated second runs (counted through those): {covered}")
famneed = sorted({(fam_of_box.get(b, '?'), e) for b, e in pairs if (b, e) not in {(x[0], x[1]) for x in covered}})
fullfam = {(fam_of_box.get(b, (open(f'{R}/ENGINES_CHECKS.txt').read() if False else '?')), e) for (b, e), (st, sha) in logs.items() if st == 'full'}
# families of check-only boxes (no production parts) from ENGINES_CHECKS.txt
if os.path.exists(f'{R}/ENGINES_CHECKS.txt'):
    for l in open(f'{R}/ENGINES_CHECKS.txt'):
        c = l.rstrip('\n').split('\t')
        if len(c) >= 4 and not l.startswith('#'): fam_of_box.setdefault(c[3], c[0])
fullfam = {(fam_of_box.get(b, '?'), e) for (b, e), (st, sha) in logs.items() if st == 'full'}
famfail = [fe for fe in famneed if fe not in fullfam]
nfull = sum(1 for v in logs.values() if v[0] == 'full'); nlight = sum(1 for v in logs.values() if v[0] == 'light'); nfail = sum(1 for v in logs.values() if v[0] == 'fail')
print(f"check logs: {len(logs)} (full ok {nfull}, light ok {nlight}, failed {nfail}); other files in checks/ (not <box>.<engine>.log, ignored): {len(other_checks)}")
print(f"production (box, engine) pairs: {len(pairs)}; without an ok check log for that engine and binary: {len(bad)} {bad[:8]}")
ownfull = [(b, e) for (b, e) in sorted(pairs) if logs.get((b, e), ('missing', None))[0] == 'full']
checkonly = sorted(set(logs) - set(pairs))
print(f"production (box, engine) pairs: {len(pairs)} = {len(ownfull)} with their own full check (incl. REFREUSE) + {len(covered)} counted through "
      f"verified gated second runs ({sum(x[2] for x in covered)} parts) + {len(pairs) - len(ownfull) - len(covered)} other; "
      f"check logs of pairs without production parts (check-only): {len(checkonly)} {checkonly[:4]}")
lightonly = [(b, e) for (b, e) in sorted(pairs) if logs.get((b, e), ('missing', None))[0] == 'light' and (b, e) not in {(x[0], x[1]) for x in covered}]
print(f"production (box, engine) pairs with only a LIGHT check (for LTSB packages rc11 gate condition 2 needs 0): {len(lightonly)} {lightonly[:8]}")
print(f"(family, engine) pairs used: {famneed}; without an ok FULL check (lwe8 identity{' + lwe10b LTSB identity' if LTSB else ''}): {famfail}")
if LTSB and os.path.exists(f'{R}/BOX_GATES.txt'):
    bg = open(f'{R}/BOX_GATES.txt').read().split('\n')
    print(f"fleet BOX_GATES.txt line 2 (parts on boxes whose full check has not passed): {bg[1] if len(bg) > 1 else '?'}")
print(f"check logs with a MISMATCH or DIFFER line (alarm, whether or not their parts are covered by second runs): {mism}")
print("PROVENANCE " + ("OK" if not bad and not famfail and not exe_bad_unc and not env_bad_unc and not dup_diff else "INCOMPLETE"))
