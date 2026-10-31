"""Coverage for the queue run: every rep of todo_box1.txt must appear in exactly one complete 'J' line (10 fields)
in out/*.out; reports SOL lines and totals. Usage: python3 collect.py"""
import glob, os
D = os.path.dirname(os.path.abspath(__file__))
todo = [int(l.split()[1], 16) for l in open(os.path.join(D, "todo_box1.txt"))]
seen = {}; sols = []; dup = conflict = 0
for f in sorted(glob.glob(os.path.join(D, "out", "*.out"))):
    for l in open(f):
        t = l.split()
        if not t: continue
        if t[0] == "J" and len(t) == 10:
            x = int(t[1], 16); v = tuple(int(u) for u in t[2:])
            if x in seen:
                dup += 1
                if seen[x] != v: conflict += 1
            seen[x] = v
        elif t[0] == "SOL":
            sols.append(l.strip())
vals = [seen[x] for x in todo if x in seen]
print("todo reps", len(todo), "covered", len(seen), "missing", len(set(todo) - set(seen)), "extra", len(set(seen) - set(todo)),
      "duplicates", dup, "conflicts", conflict)
print("pairs", sum(v[3] for v in vals), "passing", sum(v[4] for v in vals), "nodes", sum(v[5] for v in vals),
      "nodes2", sum(v[6] for v in vals), "solutions", sum(v[7] for v in vals), "SOL lines", len(sols))
for s in sols[:20]: print(s)
