"""Compare gtest4 and csp5p on P/Z instances (runs/pz) and summarise E-mode planted runs (runs/plantE)."""
import sys, os, re, glob
d = sys.argv[1]
n = 0; dis = []
for f in sorted(glob.glob(os.path.join(d, 'pz', '*.gt4'))):
    base = f[:-4]
    g = open(f).read(); c = open(base + '.csp').read() if os.path.exists(base + '.csp') else ''
    mg = re.search(r'found=(\d).*sols=(\d+) hash=([0-9a-f]+).* t=([0-9.]+)s', g)
    mc = re.search(r'nsol=(\d+)\+? hash=([0-9a-f]+).*wall=([0-9.]+)', c)
    pf = re.search(r'planted_found=(\d)', c)
    if not mg or not mc: dis.append((os.path.basename(base), 'missing', bool(mg), bool(mc))); continue
    n += 1
    ok = mg.group(2) == mc.group(1) and mg.group(3) == mc.group(2)
    if os.path.basename(base).startswith('P'): ok = ok and pf is not None and pf.group(1) == mg.group(1)
    line = "%-14s gtest4 sols=%-7s hash=%s found=%s t=%6.1fs | csp5p nsol=%-7s hash=%s found=%s wall=%6.1fs %s" % (
        os.path.basename(base), mg.group(2), mg.group(3), mg.group(1), float(mg.group(4)), mc.group(1), mc.group(2), pf.group(1) if pf else '-', float(mc.group(3)), 'OK' if ok else 'DISAGREE')
    print(line)
    if not ok: dis.append(line)
print("P/Z instances compared:", n, " disagreements/missing:", len(dis))
for x in dis: print("  ", x)
# E-mode planted (csp5p only)
tot = good = 0
for f in sorted(glob.glob(os.path.join(d, 'plantE', 'ch_???.csp'))):
    for l in open(f):
        m = re.search(r'nsol=(\d+) hash=([0-9a-f]+).*planted_hash=([0-9a-f]+).*planted_found=(\d)', l)
        if not m: continue
        tot += 1
        if m.group(1) == '1' and m.group(2) == m.group(3) and m.group(4) == '1': good += 1
        else: print("  planted-E anomaly:", l.strip()[:200])
print("E-mode planted (pi0 uniformly random, not normal): %d instances, unique solution = planted in %d" % (tot, good))
