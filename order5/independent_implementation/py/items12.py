import sys, itertools, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gf import *
NZ = [1, W, W2]
def pat_w(n):  # norm pattern -> weight pattern
    return [0 if y == 0 else (4 if y == 1 else 2) for y in n]
Mn = {}
for n in itertools.product([0, 1, W, W2], repeat=7):
    Mn[n] = M_of_weights(pat_w(n))
def scale(c, n):
    return tuple(MUL[c][y] for y in n)
R_pats = []
R_count = 0
iso_count = 0
iso_pats = []
for n, m in Mn.items():
    s = 0
    for y in n: s ^= y
    nnz = sum(1 for y in n if y)
    if s == 1:
        ok = Mn[n] >= 12 and Mn[scale(W, n)] >= 14 and Mn[scale(W2, n)] >= 14
        if ok:
            R_pats.append(n); R_count += 5 ** nnz
    elif s == 0 and nnz > 0:
        ok = all(Mn[scale(c, n)] >= 16 for c in NZ)
        if ok:
            iso_pats.append(n); iso_count += 5 ** nnz
print("|R| =", R_count, "from", len(R_pats), "norm patterns")
print("isotropic count =", iso_count, "from", len(iso_pats), "norm patterns")
from collections import Counter
print("R support sizes:", Counter(sum(1 for y in n if y) for n in R_pats))
print("R weight-pattern multiset (sorted wts) counts:", Counter(tuple(sorted(pat_w(n))) for n in R_pats))
print("iso support sizes:", Counter(sum(1 for y in n if y) for n in iso_pats))
# M distribution over all weight patterns
print("max M over all weight patterns:", max(Mn.values()))
print("M histogram:", sorted(Counter(Mn.values()).items()))
