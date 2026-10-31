"""Y23 coverage ledger over the local part (out/ledger/local_join_outputs/j_*.txt) and the box part
(out/box/att_*/j_*.txt copied back): every rep of out/xreps23.txt must have a complete J line (10 fields);
duplicates must agree; reports SOL lines, totals, depth profile."""
import glob
D = "<HOME>/c72_indep/y23/out/"
reps = [int(l.split()[1], 16) for l in open(D + "xreps23.txt")]
assert len(set(reps)) == len(reps)
parts = {"local": sorted(glob.glob(D + "ledger/local_join_outputs/j_*.txt")), "box": sorted(glob.glob(D + "box/att_*/j_*.txt"))}
seen = {}; src = {}; dup = conflict = 0; sols = []; depth = {}
stats = {}
for name, files in parts.items():
    cnt = 0; cpu = 0.0; ndone = 0
    for f in files:
        for l in open(f):
            t = l.split()
            if not t: continue
            if t[0] == "J" and len(t) == 10:
                x = int(t[1], 16); v = tuple(int(u) for u in t[2:])
                if x in seen:
                    dup += 1
                    if seen[x] != v: conflict += 1
                else:
                    cnt += 1
                seen[x] = v; src[x] = name
            elif t[0] == "SOL":
                sols.append((name, l.strip()))
            elif t[0] == "DONE" and len(t) >= 7:
                cpu += float(t[6]); ndone += 1
            elif t[0] == "nodes" and t[1] == "depth" and len(t) == 4:
                depth[int(t[2])] = depth.get(int(t[2]), 0) + int(t[3])
    stats[name] = (len(files), cnt, ndone, cpu)
for name, (nf, cnt, nd, cpu) in stats.items():
    print("%-5s files %d  new reps %d  DONE lines %d  cpu %.1f" % (name, nf, cnt, nd, cpu))
missing = set(reps) - set(seen)
vals = [seen[x] for x in reps if x in seen]
print("reps", len(reps), "covered", len(seen), "missing", len(missing), "extra", len(set(seen) - set(reps)),
      "duplicates", dup, "conflicts", conflict)
print("X-check failures", sum(1 for v in vals if v[0] == 0), "| S1 empty", sum(1 for v in vals if v[1] == 0),
      "| pairs", sum(v[3] for v in vals), "passing", sum(v[4] for v in vals))
print("nodes (phase 1+3)", sum(v[5] for v in vals), "nodes2 (phase 2)", sum(v[6] for v in vals),
      "solutions", sum(v[7] for v in vals), "SOL lines", len(sols))
if depth: print("deepest depth (completed processes only)", max(depth))
for s in sols[:20]: print(s)
