"""Build separator spec files and report the subgroup of Aut(Y) preserving the pair structure."""
import sys, pickle
K = int(sys.argv[1]); DIR = sys.argv[2]
sys.path.insert(0, DIR + "/src")
from codes import *
n = 36; FULL = (1 << n) - 1
G = read_code36(K)
words = span(G)
A = pickle.load(open(DIR + "/out/aut.pkl", "rb")); grp = A["grp"]
S = pickle.load(open(DIR + "/out/structure.pkl", "rb")); orbs = S["orbs"]
om = [sum(1 << i for i in o) for o in orbs]
def img(T, p): return sum(1 << p[i] for i in range(n) if T >> i & 1)
def stab_of_pairs(pairs):
    key = {frozenset((a, c)) for a, c in pairs}
    return [p for p in grp if {frozenset((img(a, p), img(c, p))) for a, c in pairs} == key]
def dimY(T): return 18 - rank([g & (FULL & ~T) for g in G], n)
def write(tag, pairs):
    st = stab_of_pairs(pairs)
    info = [(wt(a), dimY(a), wt(c), dimY(c)) for a, c in pairs]
    open(DIR + "/out/sep_%s.txt" % tag, "w").write(repr({"pairs": [[a, c] for a, c in pairs]}))
    print(tag, "pairs (|A|,dimY(A),|C|,dimY(C)):", info, "preserving subgroup order", len(st), "of", len(grp))
    pickle.dump([grp.index(p) for p in st], open(DIR + "/out/sep_%s_group.pkl" % tag, "wb"))
U = lambda *ix: sum(om[i] for i in ix)
for spec in sys.argv[3:]:
    tag, kind = spec.split("=")
    if kind.startswith("T:"):
        T = int(kind[2:], 16)
        write(tag, [(FULL & ~T, T)])
    elif kind.startswith("orbits:"):
        prs = []
        for pr in kind[7:].split(";"):
            a, c = pr.split("|")
            prs.append((U(*map(int, a.split(","))), U(*map(int, c.split(",")))))
        write(tag, prs)
