"""Check completeness of the X-orbit representatives: for random engine-valid X, the designated representative of
its G-orbit (min Z, then min w) must be in the reps file, or must itself fail the engine's X-level checks."""
import sys, struct, random, subprocess, os
D = "<HOME>/c72_indep/"
env = dict(os.environ, TMPDIR=D + "tmp")
data = open(D + "out/xaction_UV.bin", "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
maps = []
off = 8
for g in range(ng):
    vals = struct.unpack("<41Q", data[off:off + 41 * 8]); off += 41 * 8
    # precompute column images for speed: image(x) = c ^ xor of col[j] for bits j of x
    rows, c = vals[:40], vals[40]
    cols = [sum(((rows[i] >> j) & 1) << i for i in range(40)) for j in range(40)]
    maps.append((cols, c))
def img(m, x):
    cols, c = m
    out = c
    j = 0
    while x:
        if x & 1: out ^= cols[j]
        x >>= 1; j += 1
    return out
reps = set(int(l.split()[1], 16) for l in open(D + "out/xreps_UV.txt"))
random.seed(int(sys.argv[1]))
nsamp = int(sys.argv[2])
# sample random X and keep engine-valid ones
cand = [random.getrandbits(40) for _ in range(nsamp * 100)]
open(D + "tmp/orbtest_cand.txt", "w").write("".join("%016x %016x\n" % (0, x) for x in cand))
out = subprocess.run(["nice", "-n", "10", D + "src/engine5", D + "out/y39_UV.eng", "feas", D + "tmp/orbtest_cand.txt", "40", "40", "-"],
                     capture_output=True, text=True, env=env).stdout
valid = [int(l.split()[2], 16) for l in out.split("\n") if l.startswith("FEAS") and l.split()[3] == "1"][:nsamp]
print("valid samples", len(valid))
ZM = (1 << 30) - 1
desig = []
for x in valid:
    best = None
    for m in maps:
        y = img(m, x)
        key = ((y & ZM) << 10) | (y >> 30)
        if best is None or key < best[0]:
            best = (key, y)
    desig.append(best[1])
inrep = [d in reps for d in desig]
missing = [d for d, f in zip(desig, inrep) if not f]
open(D + "tmp/orbtest_missing.txt", "w").write("".join("%016x %016x\n" % (0, x) for x in missing))
out = subprocess.run(["nice", "-n", "10", D + "src/engine5", D + "out/y39_UV.eng", "feas", D + "tmp/orbtest_missing.txt", "40", "40", "-"],
                     capture_output=True, text=True, env=env).stdout
missing_valid = [l for l in out.split("\n") if l.startswith("FEAS") and l.split()[3] == "1"]
print("designated rep in file:", sum(inrep), "/", len(valid), "; not in file:", len(missing),
      "; of those engine-valid (would be an ERROR):", len(missing_valid))
