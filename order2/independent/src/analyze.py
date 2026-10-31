import sys
sys.path.insert(0, "<HOME>/c72_indep/src")
from codes import *

k = int(sys.argv[1]) if len(sys.argv) > 1 else 39
G = read_code36(k)
n = 36
print("rank", rank(G, n))
for a in G:
    for b in G:
        assert dot(a, b) == 0
print("self-orthogonal: ok")
words = span(G)
wd = weight_distribution(words, n)
print("weight distribution", {i: c for i, c in enumerate(wd) if c})
ones = (1 << n) - 1
assert ones in set(words)
print("all-ones in code: ok")
