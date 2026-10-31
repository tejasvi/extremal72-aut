"""Completeness of xrepsfull representatives: for random engine-valid X, the minimum (as an integer) of its G-orbit
must be in the reps file, or must itself fail the engine's X-level checks.
usage: test_orbits_full.py DIR ENG ACT REPS NX SEED NSAMP"""
import sys, struct, random, subprocess, os
DIR, ENG, ACT, REPS, NX, SEED, NS = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
env = dict(os.environ, TMPDIR=DIR + "/tmp")
data = open(ACT, "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
assert nx == NX
maps = []
off = 8
for g in range(ng):
    vals = struct.unpack("<%dQ" % (nx + 1), data[off:off + (nx + 1) * 8]); off += (nx + 1) * 8
    rows, c = vals[:nx], vals[nx]
    maps.append(([sum(((rows[i] >> j) & 1) << i for i in range(nx)) for j in range(nx)], c))
def img(m, x):
    cols, c = m
    out = c; j = 0
    while x:
        if x & 1: out ^= cols[j]
        x >>= 1; j += 1
    return out
reps = set(int(l.split()[1], 16) for l in open(REPS))
random.seed(SEED)
cand = [random.getrandbits(NX) for _ in range(NS * 20)]
open(DIR + "/tmp/otest_cand.txt", "w").write("".join("0 %x\n" % x for x in cand))
eng = DIR + "/engine15"
out = subprocess.run(["nice", "-n", "10", eng, ENG, "feas", DIR + "/tmp/otest_cand.txt", str(NX), str(NX), "-"], capture_output=True, text=True, env=env).stdout
valid = [int(l.split()[1], 16) for l in out.split("\n") if l.startswith("F ") and l.split()[2] == "1"][:NS]
mins = [min(img(m, x) for m in maps) for x in valid]
notin = [d for d in mins if d not in reps]
open(DIR + "/tmp/otest_notin.txt", "w").write("".join("0 %x\n" % x for x in notin))
out = subprocess.run(["nice", "-n", "10", eng, ENG, "feas", DIR + "/tmp/otest_notin.txt", str(NX), str(NX), "-"], capture_output=True, text=True, env=env).stdout
bad = [l for l in out.split("\n") if l.startswith("F ") and l.split()[2] == "1"]
print("valid samples", len(valid), "; orbit minimum in reps file:", len(valid) - len(notin),
      "; not in file:", len(notin), "; of those passing the X checks (ERROR):", len(bad))
