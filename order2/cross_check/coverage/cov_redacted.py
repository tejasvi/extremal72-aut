#!/usr/bin/env python3
"""Account for input files that were edited for publication when a coverage report is re-run on this archive.

Usage: cov_redacted.py REPORT PKGDIR REDACTIONS.tsv OUT
cov_c2.py checks every file of PKGDIR/INPUTS.sha256. A few input files (for example tools/mklb.sh of the LTSB
packages) contained home paths and were edited for publication, so their sha256 differ from INPUTS.sha256.
For each such file this script requires that REDACTIONS.tsv lists it with the INPUTS.sha256 value as the original
sha256 and the file's present sha256 as the published one. If every reported mismatch is accounted for in this way,
it writes OUT with the mismatches counted as ok, the PROBLEM line removed, the verdict recomputed from the remaining
PROBLEM lines, and one note naming the accounted files. Otherwise OUT is the unchanged report.
"""
import hashlib, os, re, sys

rep, pkg, red, out = sys.argv[1:5]
txt = open(rep).read().splitlines()
inputs = {}
for line in open(os.path.join(pkg, 'INPUTS.sha256')):
    w = line.split()
    if len(w) == 2:
        inputs[w[1]] = w[0]
rows = []
if os.path.exists(red):
    for line in open(red):
        f = line.rstrip('\n').split('\t')
        if len(f) >= 3 and not line.startswith('#'):
            rows.append((f[0], f[1], f[2]))
def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()
acc, other = [], False
newtxt = []
for l in txt:
    m = re.match(r"^PROBLEM: INPUTS\.sha256 mismatch: \[(.*)\]$", l)
    if m:
        names = [x.strip().strip("'\"") for x in m.group(1).split(',') if x.strip()]
        ok = True
        for n in names:
            p = os.path.join(pkg, n)
            cur = sha(p) if os.path.exists(p) else None
            hit = [r for r in rows if r[0].endswith('/' + os.path.basename(os.path.normpath(pkg)) + '/' + n)
                   and r[1] == inputs.get(n) and r[2] == cur]
            if not hit:
                ok = False
        if ok:
            acc += names
            continue
        other = True
    newtxt.append(l)
if acc:
    k = len(acc)
    newtxt = [re.sub(r'INPUTS ok (\d+) bad (\d+)', lambda m: f'INPUTS ok {int(m.group(1)) + k} bad {int(m.group(2)) - k}', l)
              if l.startswith('package ') else l for l in newtxt]
    problems = [l for l in newtxt if l.startswith('PROBLEM')]
    newtxt = [l for l in newtxt if not l.startswith('VERDICT')]
    newtxt.append('note: input files edited for publication, accounted for through REDACTIONS.tsv: ' + ', '.join(acc))
    newtxt.append('VERDICT ' + ('FAIL' if problems else 'PASS'))
open(out, 'w').write('\n'.join(newtxt) + '\n')
print('accounted:', ', '.join(acc) if acc else 'none')
