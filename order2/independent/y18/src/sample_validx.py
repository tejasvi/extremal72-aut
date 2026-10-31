"""Write random X-prefixes (nX bits) passing the engine's X-level checks."""
import sys, random, subprocess, os
DIR, eng, nX, nwant, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
env = dict(os.environ, TMPDIR=DIR + "/tmp")
random.seed(seed)
out = []
tries = 0
while len(out) < nwant and tries < 20:
    tries += 1
    cand = [random.getrandbits(nX) for _ in range(max(1000, nwant * 50))]
    open(DIR + "/tmp/cand.txt", "w").write("".join("0 %x\n" % x for x in cand))
    res = subprocess.run(["nice", "-n", "10", DIR + "/src/engine10", eng, "feas", DIR + "/tmp/cand.txt", str(nX), str(nX), "-"],
                         capture_output=True, text=True, env=env).stdout
    out += [l.split()[1] for l in res.split("\n") if l.startswith("F ") and l.split()[2] == "1"]
open(sys.argv[6], "w").write("".join("0 %s\n" % x for x in out[:nwant]))
print("wrote", min(nwant, len(out)))
