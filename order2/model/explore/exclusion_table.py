# Markdown table of the project's exclusion tiers per code (definition of 2026-10-22), read from the RUN_SUMMARY files
# (runs2/fleet/<pkg>/ and runs2/<code>/, written by src/fleet_runsummary.sh and src/own_gate_block.py).
#   tier B "excluded": all parts DONE, 0 solutions, check_box OK on every box, engine gate passed, xcheck 8/8 identical
#          (or Y29's 20/20 gate rerun), audit coverage PASS (coverage-check's cov_all.sh; its manifest equals mine);
#   tier A "excluded, independently re-searched": tier B plus the separate method's report (<HOME>/c72_indep).
# Usage: python -I exclusion_table.py
import glob, re, runpy

R = '<HOME>/c72/explore/runs2'
EC = runpy.run_path('<HOME>/c72/explore/src/excl_common.py')


def field(line, key):
    m = re.search(key + r': ([^;]*)', line)
    return m.group(1).strip() if m else '?'


def get(t, pat):
    m = re.search(pat, t, re.M)
    return m.group(1) if m else '?'


rows = []
for f in sorted(glob.glob(f'{R}/fleet/*/RUN_SUMMARY.txt')) + [f'{R}/{d}/RUN_SUMMARY.txt' for d in
                                                               ('y8', 'y22', 'y23', 'y4', 'y5b', 'y1b', 'y29')]:
    t = open(f).read(); fleet = '/fleet/' in f; pkg = f.split('/')[-2]
    c = get(t, r'^(EXCLUSION CRITERIA.*)$'); tier = get(t, r"^TIER \(project's definition of 2026-10-22\): (.*)$")
    if fleet:
        code = int(get(t, r'^Y(\d+) '))
        eng = ', '.join(dict.fromkeys(f'{m.group(1)} {m.group(2)}'
                                      for m in re.finditer(r'^parts on (\S+) \S+: (\d+)', t, re.M)))
        xc = get(t, r'^xcheck (\d+/8) identical')
        chk = field(c, r'per \(family, engine\)')
    else:
        code = int(re.match(r'y(\d+)', pkg).group(1))
        eng = {'y8': 'lwe8', 'y22': 'lwe8 native', 'y23': 'lwe10 native', 'y4': 'lwe8 native 3640, lwe11 360',
               'y5b': 'lwe11 native', 'y1b': 'lwe11 native, lwe10/lwe11 portable', 'y29': 'lwe10 860, lwe11b 3140'}[pkg]
        xc = '20/20 (gate lwe8 parts)' if pkg == 'y29' else get(t, r'XCHECK8\.txt\): xcheck (\d+/8) identical')
        chk = field(c, r'check_box ok[^:]*')
    parts = re.search(r'^parts: (\d+) complete, missing (\d+), bad (\d+)', t, re.M)
    rows.append((code, ('fleet ' if fleet else 'runs2/') + pkg,
                 f'{parts.group(1)}/{int(parts.group(1)) + int(parts.group(2))}, sol {"0" if field(c, "0 solutions") == "yes" else "?"}',
                 eng, chk, field(c, 'gate'), xc, field(c, 'audit coverage'), field(c, 'independent re-search'), tier))
ist = EC['indep'](39)[0]
y39man = get(open('<HOME>/c72/explore/runs/y39/SUMMARY.txt').read(),
             r'^sha256 of sorted per-part sha256 list: ([0-9a-f]{64})')   # part-order definition (see the correction line)
ast = EC['audit']('y39', y39man)[0]
rows.append((39, 'runs/y39', '2000/2000, sol 0', 'lwe5 (LTS-1, local)', 'n/a (local, before check_box; inputs '
             're-verified by the audit, F-L4)', 'n/a (lwe5; audit reruns with lwe8+SYMFILE and lwe5: 6/6 identical)',
             'n/a (3 audit reruns)', ast, ist + ' (+ parity certificate, MATH_REPORT 4.3)',
             'A by equivalents (production run predates check_box/gate/xcheck)'))
# package variants (e.g. y32 and y32-lb): a code is excluded through ONE complete package, the one with the best tier;
# parts of two variants are never merged (each RUN_SUMMARY covers exactly one package's parts)
def rank(r):
    t = r[9]
    return (0 if t.startswith('A') else 1 if t.startswith('B') else 2, r[1])
best = {}
for r in rows:
    best.setdefault(r[0], []).append(r)
rows = []
for code, rs in best.items():
    rs.sort(key=rank)
    other = '; '.join(f'{x[1]}: {x[9]}' for x in rs[1:])
    rows.append(rs[0] + (other or '-',))
print('| code | run | parts, sol | engines (parts) | check_box | gate | xcheck | audit coverage | independent re-search | tier | other complete variants |')
print('|---|---|---|---|---|---|---|---|---|---|---|')
for r in sorted(rows):
    print(f'| Y{r[0]} | ' + ' | '.join(str(x) for x in r[1:]) + ' |')
cnt = {}
for r in rows:
    k = r[9].split(' (')[0] if not r[9].startswith('A by') else 'A by equivalents'
    cnt.setdefault(k, []).append(f'Y{r[0]}')
print()
for k in sorted(cnt):
    print(f'- {k}: {len(cnt[k])} ({", ".join(sorted(cnt[k], key=lambda y: int(y[1:])))})')
