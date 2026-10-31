import sys
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from codes import *
G = read_code36(22)
words = span(G)
S = [v for v in words if 0 < wt(v) <= 10]
assert rank(S, 36) == 18
n = 36 + len(S)
lines = ["n=%d g" % n]
for j, v in enumerate(S):
    lines.append("%d: %s;" % (36 + j, " ".join(str(i) for i in range(36) if v >> i & 1)))
lines[-1] = lines[-1][:-1] + "."
print("\n".join(lines))
print("f=[0:35|%d:%d]" % (36, n - 1))
print("x")
print("q")
