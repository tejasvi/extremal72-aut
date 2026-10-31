"""Compare gtest4 (E mode) and csp5p (COUNT=1, E mode) results chunk by chunk.  Usage: compare.py RUNDIR"""
import sys, os, re, glob, statistics
d = sys.argv[1]
rows = []; dis = []; missing = []
for ch in sorted(glob.glob(os.path.join(d, 'ch_???'))):
    lines = [l for l in open(ch)]
    g = {}
    if os.path.exists(ch + '.gt4'):
        for l in open(ch + '.gt4'):
            m = re.match(r'code (\d+) .*sols=(\d+) hash=([0-9a-f]+).* t=([0-9.]+)s', l)
            if m: g[int(m.group(1))] = (int(m.group(2)), m.group(3), float(m.group(4)))
    c = []
    if os.path.exists(ch + '.csp'):
        for l in open(ch + '.csp'):
            m = re.match(r'id=(\S+) res=(\S+) nsol=(\d+)\+? hash=([0-9a-f]+) nodes=(\d+) wall=([0-9.]+)', l)
            if m: c.append((m.group(1), m.group(2), int(m.group(3)), m.group(4), int(m.group(5)), float(m.group(6))))
    for i, l in enumerate(lines):
        idm = re.search(r'id=(\S+)', l); cid = idm.group(1) if idm else '%s:%d' % (os.path.basename(ch), i)
        gi = g.get(i); ci = next((x for x in c if x[0] == cid), None)
        if gi is None or ci is None: missing.append((cid, gi is None, ci is None)); continue
        rows.append((cid, gi, ci))
        if gi[0] != ci[2] or gi[1] != ci[3]: dis.append((cid, gi, ci))
print("compared", len(rows), "codes; missing", len(missing), "; DISAGREEMENTS", len(dis))
for x in dis[:20]: print("  DISAGREE", x)
for x in missing[:10]: print("  missing (gt4 missing, csp missing):", x)
if rows:
    sat = sum(1 for r in rows if r[1][0] > 0)
    print("codes with solutions (both):", sat)
    tg = [r[1][2] for r in rows]; tc = [r[2][5] for r in rows]
    print("gtest4 t: median %.2f mean %.2f max %.2f | csp5p wall: median %.2f mean %.2f max %.2f" % (statistics.median(tg), statistics.mean(tg), max(tg), statistics.median(tc), statistics.mean(tc), max(tc)))
