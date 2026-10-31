"""Max total node entries per part (sum over all LEVEL nodes + leaves = kids[NLEV-1]) per completed code: an upper bound
on symmetry-test calls (and so on lwe8's 32-bit stamp increments) for any rerun of a part with the same command line.
usage: maxnodes.py CODE PARTSDIR [CODE PARTSDIR ...]"""
import sys, os, re
re_lev = re.compile(r'^LEVEL (\d+) kt \d+ ncons \d+ nodes (\d+) kids (\d+)')
args = sys.argv[1:]
for code, d in zip(args[::2], args[1::2]):
    best = (0, None); tot = 0; n = 0
    for fn in os.listdir(d):
        if not re.match(r'^p\d+\.log$', fn): continue
        lev = {}
        for ln in open(os.path.join(d, fn)):
            m = re_lev.match(ln)
            if m: lev[int(m.group(1))] = (int(m.group(2)), int(m.group(3)))
        if not lev: continue
        last = max(lev)
        s = sum(v[0] for v in lev.values()) + lev[last][1]
        n += 1
        if s > best[0]: best = (s, fn)
    print(f'{code}: parts {n}, max node entries per part {best[0]:.3e} ({best[1]}), {best[0] / 2**32:.3f} x 2^32')
