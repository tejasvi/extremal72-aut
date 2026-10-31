"""Coverage and statistics for the Y23 join run (lines 'J x ok |S1| |S2| pairs passing nodes nodes2 nsol')."""
import glob
D = "<HOME>/c72_indep/y23/out/"
reps = [int(l.split()[1], 16) for l in open(D + "xreps23.txt")]
assert len(set(reps)) == len(reps)
seen = {}
cpu = 0.0; ndone = 0; nsol_lines = 0; depth = {}; depth2 = {}
for f in sorted(glob.glob(D + "join/j_*.txt")):
    for l in open(f):
        t = l.split()
        if not t: continue
        if t[0] == "J":
            x = int(t[1], 16)
            assert x not in seen, "duplicate"
            seen[x] = tuple(int(v) for v in t[2:])
        elif t[0] == "DONE":
            cpu += float(t[6]); ndone += 1
        elif t[0] == "SOL":
            nsol_lines += 1; print("SOLUTION:", l.strip())
        elif t[0] == "nodes" and t[1] == "depth":
            depth[int(t[2])] = depth.get(int(t[2]), 0) + int(t[3])
        elif t[0] == "nodes2" and t[1] == "depth":
            depth2[int(t[2])] = depth2.get(int(t[2]), 0) + int(t[3])
missing = set(reps) - set(seen)
extra = set(seen) - set(reps)
vals = list(seen.values())
print("reps", len(reps), "searched", len(seen), "missing", len(missing), "extra", len(extra))
print("failed X check", sum(1 for v in vals if v[0] == 0),
      "| reps with S1 = 0:", sum(1 for v in vals if v[1] == 0),
      "| sum |S1|", sum(v[1] for v in vals), "sum |S2|", sum(v[2] for v in vals),
      "| pairs", sum(v[3] for v in vals), "passing", sum(v[4] for v in vals))
print("nodes (phase 1+3)", sum(v[5] for v in vals), "nodes2 (phase 2)", sum(v[6] for v in vals),
      "solutions", sum(v[7] for v in vals), "SOL lines", nsol_lines, "DONE lines", ndone, "cpu", round(cpu, 1))
if depth:
    print("deepest node depth", max(depth), "; nodes at depth 104:", depth.get(104, 0), "; at 119:", depth.get(119, 0))
open(D + "join_depth.txt", "w").write("\n".join("%d %d" % (d, depth[d]) for d in sorted(depth)) + "\n")
