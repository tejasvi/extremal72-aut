"""Completeness of the canonicalized Y8 X-representatives: for random engine-valid X, take the designated element
of its G-orbit (min Z, then min (beta,alpha)), move its kernel word to the canonical word with the same group element
as the canon mode, and check membership in the class files (or that the designated element fails the X checks)."""
import sys, struct, random, subprocess, os
D = "<HOME>/c72_indep/y8/"
env = dict(os.environ, TMPDIR=D + "tmp")
data = open(D + "out/xaction8.bin", "rb").read()
ng, nx = struct.unpack("<ii", data[:8])
maps = []
off = 8
for g in range(ng):
    vals = struct.unpack("<41Q", data[off:off + 41 * 8]); off += 41 * 8
    rows, c = vals[:40], vals[40]
    maps.append(([sum(((rows[i] >> j) & 1) << i for i in range(40)) for j in range(40)], c))
def img(m, x):
    cols, c = m
    out = c
    j = 0
    while x:
        if x & 1: out ^= cols[j]
        x >>= 1; j += 1
    return out
lines = open(D + "out/canon8.txt").read().split("\n")
nwd = int(lines[0]); words = []
p = 1
for i in range(nwd):
    cl, g, can = map(int, lines[p].split()); p += 1
    comps = []
    for j in range(5):
        m, c = lines[p].split(); p += 1
        comps.append((int(m, 16), int(c)))
    words.append((cl, g, can, comps))
def kernel(x):
    return [i for i, w in enumerate(words) if all(((bin(m & x).count("1") + c) & 1) == 0 for m, c in w[3])]
classes = {}
for cl in range(3):
    classes[cl] = set(int(l.split()[1], 16) for l in open(D + "out/canon8_c%d.txt" % cl))
other = set(int(l.split()[1], 16) for l in open(D + "out/canon8_other.txt"))
random.seed(int(sys.argv[1])); nsamp = int(sys.argv[2])
cand = [random.getrandbits(40) for _ in range(nsamp * 100)]
open(D + "tmp/orb8_cand.txt", "w").write("".join("0 %x\n" % x for x in cand))
out = subprocess.run(["nice", "-n", "10", D + "src/engine8", D + "out/y8_vfirst.eng", "feas", D + "tmp/orb8_cand.txt", "40", "40", "-"],
                     capture_output=True, text=True, env=env).stdout
valid = [int(l.split()[1], 16) for l in out.split("\n") if l.startswith("F ") and l.split()[2] == "1"][:nsamp]
ZM = (1 << 30) - 1
ok = bad = 0
desig_list = []
for x in valid:
    best = min((((y & ZM) << 10) | (y >> 30), y) for y in (img(m, x) for m in maps))[1]
    desig_list.append(best)
open(D + "tmp/orb8_desig.txt", "w").write("".join("0 %x\n" % x for x in desig_list))
out = subprocess.run(["nice", "-n", "10", D + "src/engine8", D + "out/y8_vfirst.eng", "feas", D + "tmp/orb8_desig.txt", "40", "40", "-"],
                     capture_output=True, text=True, env=env).stdout
dvalid = {int(l.split()[1], 16): l.split()[2] == "1" for l in out.split("\n") if l.startswith("F ")}
nfail_valid = 0
for d in desig_list:
    k = kernel(d)
    if len(k) == 1:
        cl, g, can, _ = words[k[0]]
        x2 = img(maps[g], d)
        assert kernel(x2) == [can]
        found = x2 in classes[cl]
    else:
        found = d in other
    if found: ok += 1
    elif not dvalid.get(d, False): nfail_valid += 1
    else: bad += 1
print("valid samples", len(valid), "; found in canonical class files:", ok,
      "; designated element fails X checks (orbit has no solution):", nfail_valid, "; MISSING (error):", bad)
