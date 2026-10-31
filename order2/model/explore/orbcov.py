"""Orbit coverage of a flag: for key word k0 (first word of KEY file or given), n_O(t) = |orbit(k0) cap W_t| and
the number of g in G with g^{-1} k0 in W_t (= |Stab(k0)| * n_O(t)), per dimension.
Usage: orbcov.py CI FLAGFILE K0"""
import sys, pickle
import numpy as np
D = '<HOME>/c72/explore'
ci = int(sys.argv[1]); fl = [int(x) for x in open(sys.argv[2]).read().split()[1:]]; k0 = int(sys.argv[3])
res = pickle.load(open('<HOME>/c72/c2par/invs.pkl', 'rb'))
gens = [np.array(p, dtype=np.int64) for p in res[ci]['perms']]
idp = tuple(range(36)); seen = {idp}; fr = [idp]
while fr:
    nf = []
    for p in fr:
        for g in gens:
            q = tuple(g[list(p)])
            if q not in seen: seen.add(q); nf.append(q)
    fr = nf
P = np.array(sorted(seen), dtype=np.int64); NG = len(P)
def images(v):
    out = np.zeros(NG, dtype=np.uint64)
    for j in range(36):
        if (v >> j) & 1: out |= (np.uint64(1) << P[:, j].astype(np.uint64))
    return out
O = set(int(x) for x in images(k0)); st = NG // len(O)
print(f"Y{ci} |G|={NG} |orbit(k0)|={len(O)} |Stab(k0)|={st}")
S = [0]
for j, v in enumerate(fl[:12]):
    S = S + [s ^ v for s in S]
    n = sum(1 for s in S if s in O)
    print(f"dim {j+1}: n_O = {n}, available g for component 0 = {n * st}")
