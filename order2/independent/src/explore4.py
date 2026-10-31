import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *
from autgroup import *
from collections import Counter
n = 36
G = read_code36(39)
words = span(G)
O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
m16 = sum(1 << i for i in O16); m2 = sum(1 << i for i in O2); m18 = sum(1 << i for i in O18)
for w in (8, 10, 12):
    c = Counter((wt(v & m18), wt(v & m16), wt(v & m2)) for v in words if wt(v) == w)
    print("weight", w, "(|.&O18|,|.&O16|,|.&O2|):", sorted(c.items()))
for name, m in (("O18", m18), ("O16", m16), ("O16+O2", m16 | m2), ("O18+O2", m18 | m2)):
    sub = [v for v in words if v & ~m == 0]
    print(name, "subcode dim", rank(sub, n), "wd", {i: c for i, c in enumerate(weight_distribution(sub, n)) if c})
    proj = rref([g & m for g in G], n)
    print("   projection dim", len(proj))
