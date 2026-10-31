import sys, math
sys.path.insert(0, "<HOME>/c72_indep/src")
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[0])
O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
m16 = sum(1 << i for i in O16); m2 = sum(1 << i for i in O2); m18 = sum(1 << i for i in O18)
Hw = [v for v in words if v and v & ~m18 == 0]
Rw = [v for v in words if v and v & ~m16 == 0]
Hb = rref(Hw, n); Rb = rref(Rw, n)
print("dim H", len(Hb), "dim R", len(Rb))
def split_stats(y, Sub):
    """Y_y contains Sub (a subcode disjoint from y). Basis of Y_y = Sub basis + complement.
    For each value a of syndrome on Sub, count forbidden completions on the complement."""
    xb = shortened_basis(y)
    # build basis: Sub first then complement
    basis = list(Sub)
    for x in xb:
        if rank(basis + [x], n) > len(basis): basis.append(x)
    assert len(basis) == len(xb)
    k = len(Sub)
    T = [i for i in range(n) if not y >> i & 1]
    w = wt(y)
    if w == 8: es = [0] + [(1 << a) | (1 << b) for ai, a in enumerate(T) for b in T[ai + 1:]]
    elif w == 10: es = [1 << a for a in T]
    else: es = [0]
    bad = {}
    for e in es:
        s = syndrome_of_e(e, basis)
        bad.setdefault(s & ((1 << k) - 1), set()).add(s >> k)
    m = len(basis) - k
    # parity: 1+y component; count completions with right parity: total 2^(m-1)
    return {a: len(b) for a, b in bad.items()}, m
from collections import Counter
for name, Sub, region in (("U-words vs R", Rb, m18 | m2), ("V-words vs H", Hb, m16 | m2)):
    for w in (8, 12):
        ys = [v for v in words if wt(v) == w and v & ~region == 0]
        summary = Counter()
        for y in ys:
            st, m = split_stats(y, Sub)
            zero = st.get(0, 0)
            summary[(m, zero, tuple(sorted(Counter(st.values()).items())))] += 1
        print(name, "weight", w, "count", len(ys))
        for k_, c in summary.items():
            print("   (compl dim m, #forbidden at a=0, histogram of #forbidden over a-values):", k_, "x", c)
