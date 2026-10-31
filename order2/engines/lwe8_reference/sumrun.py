"""Summarise a split run: every part log must contain DONE with the right part id; total solutions; per-level sums
of nodes / kids / symprune; total CPU seconds.  Usage: sumrun.py RUNDIR NPART"""
import sys, re, os
d = sys.argv[1]; npart = int(sys.argv[2])
missing = []; bad = []; nsol = 0; tsum = 0
lev = {}
for p in range(npart):
    fn = os.path.join(d, f'p{p}.log')
    if not os.path.exists(fn): missing.append(p); continue
    txt = open(fn).read()
    m = re.search(r'^DONE lwe nsol (\d+) time (\d+)s split (-?\d+) part (\d+)/(\d+) N (\d+)', txt, re.M)
    if not m or int(m.group(4)) != p or int(m.group(5)) != npart or 'STOPPED' in txt: bad.append(p); continue
    nsol += int(m.group(1)) + txt.count('\nSOLUTION'); tsum += int(m.group(2))
    for mm in re.finditer(r'^LEVEL (\d+) kt (\d+) ncons (\d+) nodes (\d+) kids (\d+)(?: symprune (\d+))?', txt, re.M):
        t = int(mm.group(1)); a = lev.setdefault(t, [0, 0, 0])
        a[0] += int(mm.group(4)); a[1] += int(mm.group(5)); a[2] += int(mm.group(6) or 0)
print(f"parts: {npart - len(missing) - len(bad)} complete, missing {len(missing)}, bad {len(bad)} {bad[:10]}")
print(f"solutions: {nsol}; CPU seconds (sum of part times): {tsum} (~{tsum/3600:.1f} core-h)")
for t in sorted(lev):
    print(f"  level {t}: nodes {lev[t][0]}, kids {lev[t][1]}, symprune {lev[t][2]}")
print("(levels <= split level are recounted by every part; levels > split level are disjoint sums)")
