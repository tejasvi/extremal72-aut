"""Y22 ledger: every rep of out/xreps22.txt must have exactly one complete W line (duplicates must be identical).
usage: close_ledger22.py PART=GLOB [PART=GLOB ...] [--xcheck GLOB]
W line: W x okx nreps npass nodes nsol (7 fields). Strict parsing: a line counts only if it ends with a newline and
all fields parse; files are read one by one (never concatenated: preempted files can end in NUL bytes).
--xcheck: further result files (e.g. the hostH list_f partial run), compared line by line with the ledger."""
import glob, sys
D = "<HOME>/c72_indep/y22/"


def parse(fn):
    good, sols, bad = [], [], 0
    with open(fn, "rb") as fh:
        for raw in fh:
            if raw.startswith(b"SOL"):
                sols.append(raw.decode(errors="replace").strip())
                continue
            if not raw.startswith(b"W "):
                continue
            if not raw.endswith(b"\n"):
                bad += 1
                continue
            t = raw.decode(errors="replace").split()
            try:
                assert len(t) == 7
                good.append((t[1], tuple(int(u) for u in t[2:])))
            except (AssertionError, ValueError):
                bad += 1
    return good, sols, bad


args = sys.argv[1:]
xpat = None
if "--xcheck" in args:
    k = args.index("--xcheck"); xpat = args[k + 1]; args = args[:k] + args[k + 2:]
reps = [l.split()[1] for l in open(D + "out/xreps22.txt")]
R = set(reps)
assert len(R) == len(reps) == 646691
cover, owner = {}, {}
dup_same = dup_diff = 0
sols_all = []
for spec in args:
    part, pat = spec.split("=", 1)
    files = sorted(glob.glob(pat))
    n = nb = 0; nodes = 0
    for fn in files:
        good, sols, bad = parse(fn)
        nb += bad
        sols_all += [(fn, s) for s in sols]
        for x, v in good:
            if x in cover:
                if cover[x] == v: dup_same += 1
                else: dup_diff += 1; print("CONFLICT", x, v, cover[x], owner[x], part)
                continue
            cover[x] = v; owner[x] = part; n += 1; nodes += v[3]
    print("part %-10s files %4d bad lines %d reps %7d nodes %.6e" % (part, len(files), nb, n, nodes))
missing = R - set(cover); extra = set(cover) - R
print("reps %d covered %d missing %d extra %d duplicates identical %d conflicting %d"
      % (len(R), len(set(cover) & R), len(missing), len(extra), dup_same, dup_diff))
for x in sorted(missing)[:10]: print("MISSING", x)
vals = list(cover.values())
print("okx==0: %d | solutions (W field): %d | SOL lines: %d | total nodes %.6e"
      % (sum(1 for v in vals if v[0] == 0), sum(v[4] for v in vals), len(sols_all), sum(v[3] for v in vals)))
for fn, s in sols_all[:20]: print("SOL", fn, s)
if xpat:
    xc, xb, xs = {}, 0, 0
    for fn in sorted(glob.glob(xpat)):
        good, sols, bad = parse(fn)
        xb += bad; xs += len(sols)
        for x, v in good: xc[x] = v
    both = [x for x in xc if x in cover]
    same = sum(1 for x in both if cover[x] == xc[x])
    print("cross-check: %d reps (bad lines %d, SOL lines %d); in ledger %d: identical %d, different %d"
          % (len(xc), xb, xs, len(both), same, len(both) - same))
    for x in [x for x in both if cover[x] != xc[x]][:10]: print("XDIFF", x, cover[x], xc[x])
