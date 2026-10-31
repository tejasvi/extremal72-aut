"""Coverage and totals for the Y22 run over all attempts out/att_*/w_*.txt: every line of xreps22.txt must have a
complete 'W x ok nreps npass nodes nsol' line (duplicates across attempts must agree). Reports any SOL lines.
Usage: python3 collect.py"""
import glob, os
D = os.path.dirname(os.path.abspath(__file__))
reps = [int(l.split()[1], 16) for l in open(os.path.join(D, "xreps22.txt"))]
seen = {}; sol_lines = []; cpu = 0.0; ndone = 0; maxd = 0; dup = 0; conflict = 0
for f in sorted(glob.glob(os.path.join(D, "out", "att_*", "w_*.txt"))):
    for l in open(f):
        t = l.split()
        if not t: continue
        if t[0] == "W" and len(t) == 7:
            x = int(t[1], 16)
            v = tuple(int(u) for u in t[2:])
            if x in seen:
                dup += 1
                if seen[x] != v: conflict += 1
            seen[x] = v
        elif t[0] == "SOL":
            sol_lines.append(l.strip())
        elif t[0] == "DONE" and len(t) >= 7:
            cpu += float(t[6]); ndone += 1
        elif t[0] == "nodes" and t[1] == "depth" and len(t) == 4:
            maxd = max(maxd, int(t[2]))
missing = set(reps) - set(seen)
vals = [seen[x] for x in reps if x in seen]
print("reps", len(reps), "searched", len(seen), "missing", len(missing), "extra", len(set(seen) - set(reps)),
      "duplicates", dup, "conflicting duplicates", conflict)
print("failed X check", sum(1 for v in vals if v[0] == 0), "w-orbit reps", sum(v[1] for v in vals),
      "passing", sum(v[2] for v in vals), "nodes", sum(v[3] for v in vals), "solutions", sum(v[4] for v in vals))
print("SOL lines", len(sol_lines), "DONE lines", ndone, "cpu (completed processes)", round(cpu, 1), "deepest depth", maxd)
for s in sol_lines[:20]: print(s)
