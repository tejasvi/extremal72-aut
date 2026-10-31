"""Coverage and statistics for Y8 passes (compact output lines 'F x f nodes' / 'P x ok nodes nsol')."""
import sys, glob
D = "<HOME>/c72_indep/y8/out/"
which = sys.argv[1]
def readset(path):
    return set(int(l.split()[1], 16) for l in open(path))
if which == "p1":
    tot_n = tot_f = 0; cpu = 0.0
    for cls in ("0", "1", "2"):
        reps = readset(D + "canon8_c%s.txt" % cls)
        seen = {}
        for f in glob.glob(D + "p1/c%s_*.txt" % cls):
            for l in open(f):
                t = l.split()
                if t[0] == "F":
                    x = int(t[1], 16)
                    assert x not in seen, "duplicate"
                    seen[x] = (int(t[2]), int(t[3]))
                elif t[0] == "DONE":
                    cpu += float(t[6])
                elif t[0] == "SOL":
                    raise SystemExit("unexpected SOL in pass 1")
        assert set(seen) == reps, "pass 1 coverage mismatch for class %s" % cls
        feas = sorted(x for x, (f, n) in seen.items() if f == 1)
        open(D + "p1_feasible_c%s.txt" % cls, "w").write("".join("0 %x\n" % x for x in feas))
        nn = sum(n for f, n in seen.values())
        print("class", cls, "reps", len(reps), "V-feasible", len(feas), "nodes", nn)
        tot_n += nn; tot_f += len(feas)
    print("PASS1 total nodes", tot_n, "V-feasible", tot_f, "cpu", round(cpu, 1))
else:
    tot_n = 0; cpu = 0.0; nsol = 0; ndone = 0
    for cls in ("0", "1", "2"):
        feas = readset(D + "p1_feasible_c%s.txt" % cls)
        seen = {}
        for f in glob.glob(D + "p2/c%s_*.txt" % cls):
            for l in open(f):
                t = l.split()
                if t[0] == "P":
                    x = int(t[1], 16)
                    assert x not in seen
                    seen[x] = (int(t[2]), int(t[3]), int(t[4]))
                elif t[0] == "DONE":
                    cpu += float(t[6]); ndone += 1
                elif t[0] == "SOL":
                    nsol += 1
                    print("SOLUTION LINE:", l.strip())
        missing = feas - set(seen)
        print("class", cls, "V-feasible", len(feas), "searched", len(seen), "missing", len(missing),
              "nodes", sum(v[1] for v in seen.values()), "solutions", sum(v[2] for v in seen.values()),
              "failed prefix check", sum(1 for v in seen.values() if v[0] == 0))
        tot_n += sum(v[1] for v in seen.values())
    print("PASS2 total nodes", tot_n, "SOL lines", nsol, "DONE lines", ndone, "cpu", round(cpu, 1))
