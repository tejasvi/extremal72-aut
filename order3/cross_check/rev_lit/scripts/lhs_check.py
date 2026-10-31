# Recompute LHS of the Theorem D double count, mass, self-conjugate count, histograms,
# key distinctness (64-bit hashes) and sha256 of the decompressed list. Read-only.
import sys, gzip, hashlib, collections
from fractions import Fraction as Fr
path = sys.argv[1]
h = hashlib.sha256()
cnt = collections.Counter()
n = 0
hashes = []
try:
    import numpy as np
except Exception:
    np = None
with gzip.open(path, 'rb') as f:
    for line in f:
        h.update(line)
        parts = line.split()
        key, aut, a8, sc = parts[0], int(parts[1]), int(parts[2]), int(parts[3])
        cnt[(aut, a8, sc)] += 1
        hashes.append(int.from_bytes(hashlib.blake2b(key, digest_size=8).digest(), 'little') >> 1)
        n += 1
print("lines", n)
print("sha256(decompressed)", h.hexdigest())
lhs = Fr(0); mass = Fr(0); nsc = 0; nmon = 0
beta = collections.Counter(); auth = collections.Counter()
for (aut, a8, sc), c in cnt.items():
    mult = 1 if sc == 1 else 2
    lhs += Fr(a8, 3) / aut * c * mult
    mass += Fr(3, aut) * c * mult
    nmon += c * mult
    if sc == 1: nsc += c
    assert a8 % 9 == 0
    beta[a8 // 9] += c; auth[aut] += c
print("Mon classes", nmon, "selfconj", nsc, "non-selfconj", n - nsc)
print("LHS =", lhs, "=", float(lhs))
print("mass sum_Mon 3/|Aut| =", float(mass))
print("beta hist", sorted(beta.items()))
print("aut hist", sorted(auth.items()))
if np is not None:
    a = np.array(hashes, dtype=np.int64); a.sort()
    print("duplicate 63-bit key hashes:", int((a[1:] == a[:-1]).sum()))
else:
    print("numpy missing; distinct hashes:", len(set(hashes)))
