"""Compare fleet's lwe8 cross-check reruns (results/<pkg>/xcheck/**/p<k>.log) with the production logs
(results/<pkg>/parts/p<k>.log): LEVEL/DONE/SOLUTION/SYMPRUNE lines, 'time <n>s' stripped.  Also re-derives the
seeded selection rule from SELECTION.txt (part_i = int(sha256("c2-xcheck-"+pkg+"-"+str(i)),16) mod NPART, i = 0,1,...,
skipping duplicates, until 8) and compares it with the listed parts.  For an LTSB package (PLAN.txt line LTSBFILE)
the reference is the prototype lwe10b (source bf02087e) with LTSBFILE instead of lwe8, and LBPRUNE lines are compared too.
Usage: xcheck_cmp.py PKG NPART [PKGDIR]"""
import sys, os, re, hashlib, glob
pkg, npart = sys.argv[1], int(sys.argv[2])
HERE = os.path.dirname(os.path.abspath(__file__)); O2 = os.path.dirname(os.path.dirname(HERE))   # order2/model/explore -> order2
PKGDIR = sys.argv[3] if len(sys.argv) > 3 else f'{O2}/packages/{pkg}'
LTSB = re.search(r'^LTSBFILE (\S+)', open(f'{PKGDIR}/PLAN.txt').read(), re.M) is not None
R = os.environ.get('XC_RESULTS', f'{O2}/runs/{pkg}')   # a directory with the run's records and its unpacked parts/
sel_listed = None
if os.path.exists(f'{R}/xcheck/SELECTION.txt'):
    lines = [l for l in open(f'{R}/xcheck/SELECTION.txt') if not l.startswith('#') and l.strip()]
    if lines: sel_listed = [int(x) for x in lines[-1].split()]
sel = []; i = 0
while len(sel) < 8 and i < 10000:
    k = int(hashlib.sha256(f'c2-xcheck-{pkg}-{i}'.encode()).hexdigest(), 16) % npart
    if k not in sel: sel.append(k)
    i += 1
print(f"xcheck selection: listed {sel_listed}; re-derived (no external-part skips) {sel}; "
      f"{'MATCH' if sel_listed == sel else 'DIFFERENT (check external-part skips in SELECTION.txt)'}")
def key(fn):
    return ''.join(re.sub(r'time \d+s', '', l) for l in open(fn) if l.startswith(('LEVEL', 'DONE', 'SOLUTION', 'SYMPRUNE', 'LBPRUNE')))
found = {}
for f in glob.glob(f'{R}/xcheck/**/p*.log', recursive=True):
    m = re.search(r'/p(\d+)\.log$', f)
    if m: found[int(m.group(1))] = f
ok = 0; bad = []; missing = []
for k in (sel_listed or sel):
    if k not in found: missing.append(k); continue
    xs = open(found[k]).read()
    if '\nDONE' not in '\n' + xs or 'STOPPED' in xs: missing.append(k); continue
    if key(found[k]) == key(f'{R}/parts/p{k}.log'): ok += 1
    else: bad.append(k)
n = len(sel_listed or sel)
# integrity and setup of the xcheck reruns: SHA256SUMS, engine = lwe8 (149ce3f3...), other CPU family than production
LWE8 = '149ce3f36e48d07ea266af31241d9439f22e433ab9a3074097bb9d99dd7cd8fc'
# lwe10b builds of the prototype source bf02087e shipped in alg's frozen_rc11 (gcc 15) and frozen_b5 (gcc 14)
LWE10B = {'7766661c5c1ff70be51a9ac7b76e983b68241540b62b8f871b3935edde347893', '246ceb0bbe72f7f18c541de59f5622cd75b0d2c19196e55fa1def17783ca77e1'}
import subprocess
# single-part reference engine per package (project 2026-10-26): lwe8 for the earlier plain packages, lwe10b+LTSBFILE for LTSB
# packages, lwe10 (lwe10b without LTSBFILE) for y40 (changed 2026-10-24 ~08:19Z: lwe8's 32-bit stamp, F-L2)
_pl = [c for c in (l.rstrip('\n').split('\t') for l in open(os.path.join(HERE, 'xcheck_policy.tsv')) if not l.startswith('#'))]
REFS = {c[1]: (c[2], set(c[3].split(','))) for c in _pl if len(c) >= 4 and c[0] == 'ref'}
if os.path.exists(f'{R}/xcheck/SHA256SUMS'):
    rc = subprocess.run(['sha256sum', '-c', '--quiet', 'SHA256SUMS'], cwd=f'{R}/xcheck', capture_output=True, text=True)
    print(f"xcheck SHA256SUMS: rc {rc.returncode} ({len(open(f'{R}/xcheck/SHA256SUMS').read().splitlines())} lines)")
if os.path.exists(f'{R}/xcheck/ORIGIN.tsv'):
    probs = []
    for l in open(f'{R}/xcheck/ORIGIN.tsv'):
        c = l.rstrip('\n').split('\t')
        if len(c) < 10 or l.startswith('#') or c[0].startswith('split/') or c[1].startswith('split'): continue   # split rows: src/xsplit_cmp.py
        part, xtype, eng, sha, ptype, verdict = c[0], c[2], c[3], c[4], c[7], c[9]
        if LTSB:
            if eng != 'lwe10b' or sha not in LWE10B: probs.append(f'{part}: engine {eng} {sha[:12]} (LTSB package: lwe10b expected)')
        elif pkg in REFS:
            if eng != REFS[pkg][0] or sha not in REFS[pkg][1]: probs.append(f'{part}: engine {eng} {sha[:12]} ({REFS[pkg][0]} expected for {pkg})')
        elif eng != 'lwe8' or sha != LWE8: probs.append(f'{part}: engine {eng} {sha[:12]}')
        if xtype.split('-')[0] == ptype.split('-')[0]: probs.append(f'{part}: same family {xtype} vs {ptype}')
        ex = [x for x in c[10:] if x.startswith('exe:')]; ev = [x for x in c[10:] if x.startswith('env:')]
        if ex and ex[0][4:] not in (sha, '-'): probs.append(f'{part}: measured exe {ex[0][4:16]} != {sha[:12]}')
        if ev and ev[0].startswith('env:BAD'): probs.append(f'{part}: {ev[0]}')
        k = int(part.lstrip('p'))
        mine = 'IDENTICAL' if (k in found and key(found[k]) == key(f'{R}/parts/p{k}.log')) else 'DIFFERENT'
        if verdict != mine: probs.append(f'{part}: fleet says {verdict}, mine {mine}')
    print(f"xcheck setup ({'lwe10b+LTSBFILE' if LTSB else (REFS[pkg][0] if pkg in REFS else 'lwe8 149ce3f3')}, other CPU family, fleet verdict = mine): {'OK' if not probs else probs}")
# split cross-checks (XSPLIT, 16 sub-parts): verified by src/xsplit_cmp.py for EVERY selected part with a split dir. Project
# 2026-10-26: a split part counts toward 8/8 only if src/xcheck_policy.tsv approves its class AND my check, fleet's
# split/p<k>/VERDICT.txt and coverage-check's cov_<pkg>.txt (8 of 8 selected parts identical, single or split) all say IDENTICAL;
# a part with both a single and a split rerun needs both IDENTICAL.
pol = {c[0]: c[1] for c in _pl if len(c) >= 2}
splitp = [k for k in (sel_listed or sel) if os.path.isdir(f'{R}/xcheck/split/p{k}')]
if splitp:
    spl = int(re.search(r'^SPLIT_LEVEL (\d+)', open(f'{PKGDIR}/PLAN.txt').read(), re.M).group(1))
    out = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'xsplit_cmp.py'),
                          pkg, str(npart), str(spl)] + [str(k) for k in splitp], capture_output=True, text=True).stdout
    print('\n'.join(('  ' + l) if l.startswith('p') else ('xcheck split check: ' + l) for l in out.strip().split('\n')))
    sid = [int(m.group(1)) for m in re.finditer(r'^p(\d+): IDENTICAL', out, re.M)]
    sdiff = [int(m.group(1)) for m in re.finditer(r'^p(\d+): DIFFERENT', out, re.M)]
    fleetv = {k: (open(f'{R}/xcheck/split/p{k}/VERDICT.txt').read().strip().split('\n')[-1].strip()
                  if os.path.exists(f'{R}/xcheck/split/p{k}/VERDICT.txt') else 'none') for k in splitp}
    cov = os.path.join(O2, 'cross_check', 'coverage', f'cov_{pkg}.txt')
    m8 = re.search(r'selected parts with an identical cross-check \(single or split; both identical where both exist\): (\d+) of (\d+)',
                   open(cov).read()) if os.path.exists(cov) else None
    aud8 = bool(m8) and m8.group(1) == m8.group(2)
    cls = 'split_lwe10b_ltsb' if LTSB else 'split_lwe10b_nonltsb'
    for k in sdiff:
        if k not in bad: bad.append(k)
        if k in found and k not in missing: ok -= 1   # its single rerun was counted; the split disagrees
        missing = [x for x in missing if x != k]
    fdiff = [k for k in splitp if fleetv[k] != 'IDENTICAL']
    cnt = [k for k in sid if k in missing and fleetv.get(k) == 'IDENTICAL'] if pol.get(cls) == 'approved' and aud8 else []
    ok += len(cnt); missing = [k for k in missing if k not in cnt]
    print(f"xcheck split: mine IDENTICAL {len(sid)}, DIFFERENT {sdiff}; fleet VERDICT not IDENTICAL: {fdiff}; coverage-check cov: "
          f"{m8.group(0)[-9:] if m8 else 'no split note / no cov file'}; policy {cls}: {pol.get(cls, 'missing')}; counted now: {len(cnt)}")
print(f"xcheck {ok}/{n} identical" + (f"; DIFFERENT: {bad}" if bad else "") + (f"; not yet available: {missing}" if missing else ""))
