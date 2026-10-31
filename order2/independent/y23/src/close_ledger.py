"""Y23 ledger: main-VM part (out/ledger/local_join_outputs/j_*.txt) + hostM rerun of the box part
(out/hostM_q/*.out copied from <HOME>/indep/y23q/out/). Every rep of out/xreps23.txt must have a complete J line
(10 fields); duplicates must agree; SOL lines reported; per-part totals."""
import glob, os
D = "<HOME>/c72_indep/y23/out/"
reps = [int(l.split()[1], 16) for l in open(D + "xreps23.txt")]
assert len(set(reps)) == len(reps)
local_done = set(int(l, 16) for l in open(D + "ledger/local_done.txt").read().split())
todo_box = set(int(l.split()[1], 16) for l in open(D + "ledger/todo_box1.txt"))
assert local_done.isdisjoint(todo_box) and len(local_done) + len(todo_box) == len(reps)
parts = [("main VM", sorted(glob.glob(D + "ledger/local_join_outputs/j_*.txt"))), ("hostM", sorted(glob.glob(D + "hostM_q/*.out")))]
seen = {}; owner = {}; dup = conflict = 0; sols = []
for name, files in parts:
    cnt = 0; nodes = 0; pairs = 0; npass = 0
    for f in files:
        for l in open(f):
            t = l.split()
            if not t: continue
            if t[0] == "J" and len(t) == 10:
                x = int(t[1], 16); v = tuple(int(u) for u in t[2:])
                if x in seen:
                    dup += 1
                    if seen[x] != v: conflict += 1
                    continue
                seen[x] = v; owner[x] = name; cnt += 1
                nodes += v[5] + v[6]; pairs += v[3]; npass += v[4]
            elif t[0] == "SOL":
                sols.append((name, l.strip()))
    print("%-8s files %6d reps %8d nodes %.4g pairs %.4g passing %.4g" % (name, len(files), cnt, nodes, pairs, npass))
missing = set(reps) - set(seen)
print("reps", len(reps), "covered", len(seen), "missing", len(missing), "extra", len(set(seen) - set(reps)),
      "duplicates", dup, "conflicts", conflict)
print("main-VM part owned by main VM:", sum(1 for x in local_done if owner.get(x) == "main VM"), "of", len(local_done),
      "| box part owned by hostM:", sum(1 for x in todo_box if owner.get(x) == "hostM"), "of", len(todo_box))
vals = list(seen.values())
print("X-check failures", sum(1 for v in vals if v[0] == 0), "| solutions (J field)", sum(v[7] for v in vals), "| SOL lines", len(sols))
for s in sols[:20]: print(s)
