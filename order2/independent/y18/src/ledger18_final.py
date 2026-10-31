"""Y18 final ledger over the pulled, still-compressed results (main VM, light: one process, no extraction).
usage: ledger18_final.py
Universe: out/box/xreps18.txt.gz. Queue part: J lines (10 fields) in members out/*.out of out/box/pull_*.tgz (hostF).
Stab part: JT lines (16 fields) in members stab/*/*.out of out/box/, out/box_hostM/, out/fleet14/ archives (and
out/box_hostH/ if any); per rep all NSPLIT splits must be present once with equal split-invariant fields.
Strict parsing: a line counts only if it ends with a newline and has the exact field count with integer fields.
Every rep must be covered exactly once (queue or stab); a queue line for a stab-covered rep is a cross-check only."""
import glob, gzip, os, sys, tarfile
D = "<HOME>/c72_indep/y18/out/"


def parse_lines(raw_iter, tag, nf):
    good, sols, bad = [], [], 0
    for raw in raw_iter:
        if raw.startswith(b"SOL"):
            sols.append(raw.decode(errors="replace").strip()); continue
        if not raw.startswith(tag + b" "):
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


reps = [int(l.split()[1], 16) for l in gzip.open(D + "box/xreps18.txt.gz", "rb") if l.strip()]
R = set(reps)
assert len(R) == len(reps) == 23405112, len(reps)
q, qdup_same, qdup_diff, qbad, qfiles = {}, 0, 0, 0, set()
st, sbad, sfiles, sols = {}, 0, set(), []
for box in ("box", "box_hostM", "fleet14", "box_hostH"):
    for arch in sorted(glob.glob(D + box + "/pull_*.tgz")):
        with tarfile.open(arch, "r:gz") as tf:
            for m in tf:
                if not m.isfile() or not m.name.endswith(".out"):
                    continue
                data = tf.extractfile(m).read().splitlines(keepends=True)
                key = (box, m.name)
                if m.name.startswith("out/"):
                    if key in qfiles:
                        continue
                    qfiles.add(key)
                    good, s, b = parse_lines(data, b"J", 10)
                    qbad += b; sols += [(box, m.name, x) for x in s]
                    for x, v in good:
                        if x in q:
                            if q[x] == v: qdup_same += 1
                            else: qdup_diff += 1; print("QUEUE CONFLICT %x" % x)
                        else:
                            q[x] = v
                elif m.name.startswith("stab/"):
                    if m.name in sfiles:
                        continue      # the same item file pulled twice (identical name = identical item)
                    sfiles.add(m.name)
                    good, s, b = parse_lines(data, b"JT", 16)
                    sbad += b; sols += [(box, m.name, x) for x in s]
                    for x, v in good:
                        st.setdefault(x, []).append(v)
stab = {}
for x, L in st.items():
    ns = {v[10] for v in L}; ks = sorted(v[11] for v in L)
    inv = {(v[0], v[1], v[2], v[3], v[6], v[8], v[10], v[12], v[13]) for v in L}
    if len(ns) != 1 or ks != list(range(next(iter(ns)))) or len(inv) != 1:
        print("STAB INCOMPLETE/INCONSISTENT %x: %d lines, NSPLIT %s" % (x, len(L), sorted(ns))); continue
    ok, n1, n1k, n2, p1, nodes2, nsplit, nh, nsw = inv.pop()
    s_ = lambda c: sum(v[c] for v in L)
    stab[x] = (ok, n1, n1k, n2, s_(4), s_(5), p1 + s_(7), nodes2, s_(9), nh, nsw, nsplit, s_(9))
xcheck = {x: q.pop(x) for x in list(q) if x in stab}
cover = set(q) | set(stab)
missing, extra = R - cover, cover - R
print("universe %d | queue files %d (bad lines %d) reps %d | stab item files %d (bad lines %d) reps %d"
      % (len(R), len(qfiles), qbad, len(q), len(sfiles), sbad, len(stab)))
print("covered %d, missing %d, extra %d, queue duplicates identical %d, conflicting %d"
      % (len(cover & R), len(missing), len(extra), qdup_same, qdup_diff))
for x in sorted(missing)[:20]: print("MISSING %x" % x)
qv = list(q.values())
print("queue part: reps %d nodes %.6e (phase 1+pairs %.6e, phase 2 %.6e) pairs %.6e passing %.6e ok!=1 %d solutions %d"
      % (len(qv), sum(v[5] + v[6] for v in qv), sum(v[5] for v in qv), sum(v[6] for v in qv), sum(v[3] for v in qv),
         sum(v[4] for v in qv), sum(1 for v in qv if v[0] != 1), sum(v[7] for v in qv)))
sv = list(stab.values())
print("stab part: reps %d nodes %.6e pairs %.6e passing %.6e ok!=1 %d solutions %d"
      % (len(sv), sum(v[6] + v[7] for v in sv), sum(v[4] for v in sv), sum(v[5] for v in sv),
         sum(1 for v in sv if v[0] != 1), sum(v[8] for v in sv)))
print("TOTAL nodes %.6e" % (sum(v[5] + v[6] for v in qv) + sum(v[6] + v[7] for v in sv)))
for x, v in sorted(stab.items(), key=lambda t: -t[1][1]):
    xc = ""
    if x in xcheck:
        xc = " | queue line |S1|,|S2| %s" % ("equal" if (xcheck[x][1], xcheck[x][2]) == (v[1], v[3]) else "DIFFERENT")
    print("STAB %x |S1| %d kept %d |S2| %d pairs %d passing %d nodes %d nodes2 %d solutions %d maps %d+%d splits %d%s"
          % ((x, v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11], xc)))
print("SOL lines: %d" % len(sols))
for s in sols[:20]: print("SOL", s)
print("ALL COVERED" if not missing and not extra and qdup_diff == 0 and qbad + sbad == 0 else "NOT COMPLETE")
