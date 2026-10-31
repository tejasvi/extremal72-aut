"""Y23 ledger (final). Every rep of out/xreps23.txt must be covered by exactly one of
  (1) main-VM part:   out/ledger/local_join_outputs/j_*.txt  (J lines, plain join),
  (2) hostM rerun of the box part: out/hostM_q/*.out            (J lines, join with prefilter, work queue),
  (3) heavy reps of the box part: out/hostM_stab/*.out         (JT lines, join with the Stab(X) reduction; all NSPLIT
      splits present, split-invariant fields equal; combined per rep).
Strict parsing: a line counts only if it ends with a newline and has the exact field count with integer fields.
Cross-check: hostH box results (out/hostH_box/att_*/j_*.txt) against part (2), line by line."""
import glob, sys
D = "<HOME>/c72_indep/y23/out/"
HEAVY5 = {0xc52febdd, 0xc54fbb1d, 0xc6e91bdd, 0xd1b46ef6, 0xe7c1b3b6}   # never finished anywhere with the plain join
TAIL4 = {0x4647bdb8, 0x46bfddf8, 0x477acf54, 0xc4b4af3a}                 # hostH has plain-join lines for these
HEAVY = HEAVY5 | TAIL4      # covered by the Stab(X)-reduced runs (part 3)


def parse(fn, tag, nf):
    """complete lines with tag and nf fields -> list of (x, tuple of ints); SOL lines; count of bad lines with tag"""
    good, sols, bad = [], [], 0
    with open(fn, "rb") as fh:
        for raw in fh:
            if raw.startswith(b"SOL"):
                sols.append(raw.decode(errors="replace").strip())
                continue
            if not raw.startswith(tag.encode() + b" "):
                continue
            if not raw.endswith(b"\n"):
                bad += 1
                continue
            t = raw.decode().split()
            try:
                assert len(t) == nf
                good.append((int(t[1], 16), tuple(int(u) for u in t[2:])))
            except (AssertionError, ValueError):
                bad += 1
    return good, sols, bad


reps = [int(l.split()[1], 16) for l in open(D + "xreps23.txt")]
R = set(reps)
assert len(R) == len(reps) == 1573596
local_done = set(int(l, 16) for l in open(D + "ledger/local_done.txt").read().split())
todo_box = set(int(l.split()[1], 16) for l in open(D + "ledger/todo_box1.txt"))
assert local_done.isdisjoint(todo_box) and local_done | todo_box == R
assert HEAVY <= todo_box
print("universe %d reps = main-VM part %d + box part %d (heavy %d)" % (len(R), len(local_done), len(todo_box), len(HEAVY)))

cover = {}       # x -> (part, values)
dup_same = dup_diff = 0
allsols = []
totals = {}


def add(part, x, v):
    global dup_same, dup_diff
    if x in cover:
        if cover[x] == (part, v):
            dup_same += 1
        else:
            dup_diff += 1
            print("CONFLICT", part, hex(x), v, cover[x])
        return
    cover[x] = (part, v)


q_heavy = {}
for part, pat in (("main", "ledger/local_join_outputs/j_*.txt"), ("hostM", "hostM_q/*.out")):
    files = sorted(glob.glob(D + pat))
    nb = 0
    for fn in files:
        good, sols, bad = parse(fn, "J", 10)
        nb += bad
        allsols += [(fn, s) for s in sols]
        for x, v in good:
            if part == "hostM" and x in HEAVY:
                q_heavy[x] = v          # plain-join line for a rep of part 3: cross-check only
                continue
            add(part, x, v)
    print("part %-5s files %5d bad lines %d" % (part, len(files), nb))

# part 3: combine JT splits per rep
files = sorted(glob.glob(D + "hostM_stab/*.out") + glob.glob(D + "hostM_stab/extra4/*.out"))
grp, nb = {}, 0
for fn in files:
    good, sols, bad = parse(fn, "JT", 16)
    nb += bad
    allsols += [(fn, s) for s in sols]
    for x, v in good:
        grp.setdefault(x, []).append(v)
print("part stab  files %5d bad lines %d reps %d" % (len(files), nb, len(grp)))
heavy_lines = {}
for x, L in sorted(grp.items()):
    # v = (ok, n1, n1kept, n2, npair, npass, nodes_p1, nodes_pairs, nodes2, nsol, NSPLIT, SPLIT, nh, ns)
    ns = {v[10] for v in L}
    ks = sorted(v[11] for v in L)
    inv = {(v[0], v[1], v[2], v[3], v[6], v[8], v[10], v[12], v[13]) for v in L}
    if len(ns) != 1 or ks != list(range(ns.pop())) or len(inv) != 1:
        print("STAB INCOMPLETE/INCONSISTENT", hex(x), len(L))
        continue
    ok, n1, n1k, n2, p1, nodes2, nsplit, nh, nsw = inv.pop()
    s = lambda c: sum(v[c] for v in L)
    v = (ok, n1, n1k, n2, s(4), s(5), p1 + s(7), nodes2, s(9), nh, nsw, nsplit)
    heavy_lines[x] = v
    add("stab", x, v)

missing = R - set(cover)
extra = set(cover) - R
own_ok = all(cover.get(x, ("",))[0] == "main" for x in local_done) and \
    all(cover.get(x, ("",))[0] == ("stab" if x in HEAVY else "hostM") for x in todo_box)
print("covered %d of %d, missing %d, extra %d, duplicates identical %d, conflicting %d, ownership as planned %s"
      % (len(set(cover) & R), len(R), len(missing), len(extra), dup_same, dup_diff, own_ok))
for x in sorted(missing)[:20]:
    print("MISSING", hex(x), "(heavy)" if x in HEAVY else "", "(main part)" if x in local_done else "(box part)")

for part in ("main", "hostM", "stab"):
    vs = [v for p, v in cover.values() if p == part]
    if part == "stab":
        nodes = sum(v[6] + v[7] for v in vs); pairs = sum(v[4] for v in vs); npass = sum(v[5] for v in vs)
        okf = sum(1 for v in vs if v[0] != 1); nsol = sum(v[8] for v in vs)
    else:
        nodes = sum(v[5] + v[6] for v in vs); pairs = sum(v[3] for v in vs); npass = sum(v[4] for v in vs)
        okf = sum(1 for v in vs if v[0] != 1); nsol = sum(v[7] for v in vs)
    totals[part] = nodes
    print("part %-5s reps %8d nodes %.6e pairs %.6e passing %.6e | ok!=1: %d | solutions: %d"
          % (part, len(vs), nodes, pairs, npass, okf, nsol))
print("TOTAL nodes %.6e" % sum(totals.values()))
for x, v in sorted(heavy_lines.items()):
    print("HEAVY %x: |S1| %d kept %d |S2| %d pairs %d passing %d nodes %d nodes2 %d solutions %d (Stab maps %d+%d, %d splits)"
          % ((x,) + v[1:]))
print("SOL lines in parts: %d" % len(allsols))
for fn, s in allsols[:20]:
    print("SOL", fn, s)

# cross-check against hostH (box part, plain join): line by line
cf, cf_bad, cf_sols = {}, 0, []
for fn in sorted(glob.glob(D + "hostH_box/att_*/j_*.txt")):
    good, sols, bad = parse(fn, "J", 10)
    cf_bad += bad
    cf_sols += sols
    for x, v in good:
        if x in cf and cf[x] != v:
            print("hostH INTERNAL CONFLICT", hex(x))
        cf[x] = v
both = [x for x in cf if x in cover and cover[x][0] == "hostM"]
same = sum(1 for x in both if cover[x][1] == cf[x])
print("hostH cross-check: hostH reps %d (bad lines %d, SOL lines %d); in hostM part %d: identical %d, different %d; "
      "hostH reps outside the box part %d; box-part reps (excluding heavy) without a hostH line %d"
      % (len(cf), cf_bad, len(cf_sols), len(both), same, len(both) - same, len(set(cf) - todo_box),
         len((todo_box - HEAVY) - set(cf))))
for x in [x for x in both if cover[x][1] != cf[x]][:20]:
    print("DIFF", hex(x), "hostM", cover[x][1], "hostH", cf[x])
for x in sorted(HEAVY):
    msg = "heavy %x: in hostH results %s" % (x, x in cf)
    if x in cf and x in heavy_lines:
        v = heavy_lines[x]
        msg += "; |S1|,|S2| stab run (%d, %d) vs hostH (%d, %d) %s" % (v[1], v[3], cf[x][1], cf[x][2],
                                                                     "equal" if (v[1], v[3]) == (cf[x][1], cf[x][2]) else "DIFFERENT")
    if x in q_heavy:
        msg += "; hostM plain-join line %s hostH" % ("identical to" if x in cf and q_heavy[x] == cf[x] else "DIFFERS from")
    print(msg)
