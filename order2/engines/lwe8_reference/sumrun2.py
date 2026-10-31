"""Summarise a split run of lwe8: every part log must contain DONE with its part id; total solutions; per-level
sums (nodes, kids, symprune, ltsprune, lhprune); CPU seconds.  Usage: sumrun2.py RUNDIR NPART"""
import sys, re, os
d = sys.argv[1]; npart = int(sys.argv[2])
missing, bad = [], []; nsol = 0; tsum = 0; lev = {}
for p in range(npart):
    fn = os.path.join(d, f'p{p}.log')
    if not os.path.exists(fn): missing.append(p); continue
    txt = open(fn).read()
    m = re.search(r'^DONE lwe nsol (\d+) time (\d+)s split (-?\d+) part (\d+)/(\d+) N (\d+)', txt, re.M)
    if not m or int(m.group(4)) != p or int(m.group(5)) != npart or 'STOPPED' in txt: bad.append(p); continue
    nsol += int(m.group(1)) + txt.count('\nSOLUTION') + txt.startswith('SOLUTION'); tsum += int(m.group(2))
    for mm in re.finditer(r'^LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+) kids (\d+) symprune (\d+) ltsprune (\d+) lhprune (\d+)', txt, re.M):
        a = lev.setdefault(int(mm.group(1)), [0] * 5)
        for k in range(5): a[k] += int(mm.group(2 + k))
print(f"parts: {npart - len(missing) - len(bad)} complete, missing {len(missing)}, bad {len(bad)} {bad[:10]}")
print(f"solutions: {nsol}; CPU seconds (sum of part times): {tsum} (~{tsum/3600:.1f} core-h)")
for t in sorted(lev):
    print(f"  level {t}: nodes {lev[t][0]}, kids {lev[t][1]}, lhprune {lev[t][4]}")
print("(levels <= split level are recounted by every part; levels > split level are disjoint sums)")
