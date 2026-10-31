"""For X-prefixes (40-bit), compute a_h = B(h, R') for all H' words (from the Z variables) and report the kernel
words of a|_{H'} (h with a_h = 0)."""
import sys, pickle
sys.path.insert(0, "<HOME>/c72_indep/y8/src")
from problem import *
from y8_struct import *
from linalg import Elim
P = Problem(read_code36(8), 36, 16)
FS = P.FS
pk = pickle.load(open(sys.argv[1], "rb"))
vf = pk["var_funcs"]
nd = len(P.diag)
E = Elim()
for t, (f, c) in enumerate(P.diag): E.add(f, 1 << t)
for i in range(40): E.add(vf[i], 1 << (nd + i))
dconst = sum(1 << t for t, (f, c) in enumerate(P.diag) if c)
Hw = [v for v in P.words if v and v & ~m18 == 0]
aexpr = {}
for h in Hw:
    rows = []
    for r in pk["Rb"]:
        combo, resid = E.express(FS.functional(h, r))
        assert resid == 0
        rows.append((combo >> nd, bin(combo & dconst & ((1 << nd) - 1)).count("1") & 1))
    aexpr[h] = rows
def kernel(x):
    return [h for h in Hw if all(((bin(r & x).count("1") + c) & 1) == 0 for (r, c) in aexpr[h])]
if __name__ == "__main__":
    for l in open(sys.argv[2]):
        x = int(l.split()[1], 16)
        k = kernel(x)
        print("%016x %016x %s" % (0, x, ",".join("%x:%d" % (h, wt(h)) for h in k)))
