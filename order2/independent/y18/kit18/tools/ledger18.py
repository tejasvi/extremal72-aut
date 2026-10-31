#!/usr/bin/env python3
"""Y18 ledger: every rep of xreps18.txt must be covered exactly once, by
  (1) the queue run: out/*.out (J lines, join), or
  (2) Stab(X)-reduced runs: stab/*/*.out (JT lines; all NSPLIT splits present, split-invariant fields equal),
      in which case a queue line for the same rep, if any, is only a cross-check (|S1|, |S2| must agree).
Strict parsing: a line counts only if it ends with a newline and has the exact field count with integer fields;
files are read one by one. usage: ledger18.py [KITDIR]"""
import glob, os, sys
K = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def parse(fn, tag, nf):
    good, sols, bad = [], [], 0
    with open(fn, "rb") as fh:
        for raw in fh:
            if raw.startswith(b"SOL"):
                sols.append(raw.decode(errors="replace").strip()); continue
            if not raw.startswith(tag.encode() + b" "):
                continue
            if not raw.endswith(b"\n"):
                bad += 1; continue
            t = raw.decode(errors="replace").split()
            try:
                assert len(t) == nf
                good.append((int(t[1], 16), tuple(int(u) for u in t[2:])))
            except (AssertionError, ValueError):
                bad += 1
    return good, sols, bad


reps = [int(l.split()[1], 16) for l in open(os.path.join(K, "xreps18.txt")) if l.strip()]
R = set(reps)
assert len(R) == len(reps)
sols_all = []
# part 2 first: which reps are covered by Stab(X) runs
grp, nb2 = {}, 0
sfiles = sorted(glob.glob(os.path.join(K, "stab", "*", "*.out")))
for fn in sfiles:
    good, sols, bad = parse(fn, "JT", 16)
    nb2 += bad; sols_all += [(fn, s) for s in sols]
    for x, v in good:
        grp.setdefault(x, []).append(v)
stab = {}
for x, L in grp.items():
    ns = {v[10] for v in L}; ks = sorted(v[11] for v in L)
    inv = {(v[0], v[1], v[2], v[3], v[6], v[8], v[10], v[12], v[13]) for v in L}
    if len(ns) != 1 or ks != list(range(ns.pop())) or len(inv) != 1:
        print("STAB INCOMPLETE/INCONSISTENT %x (%d lines)" % (x, len(L))); continue
    ok, n1, n1k, n2, p1, nodes2, nsplit, nh, nsw = inv.pop()
    s = lambda c: sum(v[c] for v in L)
    stab[x] = (ok, n1, n1k, n2, s(4), s(5), p1 + s(7), nodes2, s(9), nh, nsw, nsplit)
# part 1
cover, dup_same, dup_diff, nb1, xq = {}, 0, 0, 0, {}
qfiles = sorted(glob.glob(os.path.join(K, "out", "*.out")))
for fn in qfiles:
    good, sols, bad = parse(fn, "J", 10)
    nb1 += bad; sols_all += [(fn, s) for s in sols]
    for x, v in good:
        if x in stab:
            xq[x] = v; continue
        if x in cover:
            if cover[x] == v: dup_same += 1
            else: dup_diff += 1; print("CONFLICT %x" % x)
            continue
        cover[x] = v
for x in stab:
    cover[x] = ("stab",) + stab[x]
missing = R - set(cover); extra = set(cover) - R
print("reps %d; queue files %d (bad lines %d), stab files %d (bad lines %d, reps %d)"
      % (len(R), len(qfiles), nb1, len(sfiles), nb2, len(stab)))
print("covered %d, missing %d, extra %d, duplicates identical %d, conflicting %d"
      % (len(set(cover) & R), len(missing), len(extra), dup_same, dup_diff))
for x in sorted(missing)[:20]: print("MISSING %x" % x)
qv = [v for x, v in cover.items() if x not in stab]
print("queue part: reps %d nodes %.6e pairs %.6e passing %.6e ok!=1 %d solutions %d"
      % (len(qv), sum(v[5] + v[6] for v in qv), sum(v[3] for v in qv), sum(v[4] for v in qv),
         sum(1 for v in qv if v[0] != 1), sum(v[7] for v in qv)))
for x, v in sorted(stab.items()):
    xc = ""
    if x in xq:
        xc = "; queue line |S1|,|S2| %s" % ("equal" if (xq[x][1], xq[x][2]) == (v[1], v[3]) else "DIFFERENT")
    print("STAB %x: |S1| %d kept %d |S2| %d pairs %d passing %d nodes %d nodes2 %d solutions %d (maps %d+%d, %d splits)%s"
          % ((x,) + v[1:] + (xc,)))
print("stab part: reps %d nodes %.6e solutions %d" % (len(stab), sum(v[6] + v[7] for v in stab.values()),
                                                      sum(v[8] for v in stab.values())))
print("SOL lines: %d" % len(sols_all))
for fn, s in sols_all[:20]: print("SOL", fn, s)
print("ALL COVERED" if not missing and not extra and dup_diff == 0 and nb1 + nb2 == 0 else "NOT COMPLETE")
