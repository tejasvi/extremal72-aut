"""Search coordinate sets T (|T| <= 18) with large dim Y(T) (subcode supported in T), grown from unions of
weight-8 supports; dim Y(T) = 18 - rank(generator matrix restricted to the complement of T).
Report cross dimension d(T) * (d(T) + 18 - |T|) (= dim Y(T) * dim Y(T^c)) and the G-orbit / setwise stabilizer of T."""
import sys, pickle, itertools
K = int(sys.argv[1]); DIR = sys.argv[2]
sys.path.insert(0, DIR + "/src")
from codes import *
n = 36
G = read_code36(K)
words = span(G)
W8 = [v for v in words if wt(v) == 8]
A = pickle.load(open(DIR + "/out/aut.pkl", "rb"))
grp = A["grp"]
FULL = (1 << n) - 1
def dimY(T):
    comp = FULL & ~T
    return 18 - rank([g & comp for g in G], n)
cache = {}
def score(T):
    if T in cache: return cache[T]
    d = dimY(T)
    s = (d * (d + 18 - wt(T)), d)
    cache[T] = s
    return s
# beam search: start from unions of two w8 words; extend by w8 words; keep the best by cross score per size
level = set()
for a, b in itertools.combinations(W8, 2):
    T = a | b
    if wt(T) <= 16: level.add(T)
allT = set(level)
for it in range(4):
    # keep top 3000 of this level by score
    lv = sorted(level, key=lambda T: score(T), reverse=True)[:3000]
    nxt = set()
    for T in lv:
        for c in W8:
            T2 = T | c
            if T2 != T and wt(T2) <= 18 and T2 not in allT:
                nxt.add(T2)
    allT |= nxt
    level = nxt
res = sorted(((score(T)[0], score(T)[1], wt(T), T) for T in allT), reverse=True)
out = []
done = set()
for cross, d, sz, T in res:
    if T in done or cross < 12: continue
    orb = {sum(1 << p[i] for i in range(n) if T >> i & 1) for p in grp}
    done |= orb
    nw8 = sum(1 for v in W8 if v & ~T == 0)
    out.append((cross, d, sz, nw8, len(orb), len(grp) // len(orb), T))
    if len(out) >= 20: break
print("Y%d |G|=%d candidates (cross, dim Y(T), |T|, #w8 in T, |orbit of T|, |Stab(T)|):" % (K, len(grp)))
for o in out:
    print("  cross %2d  dim %d  |T| %2d  w8 %3d  orbit %5d  stab %5d  T=%x" % o)
pickle.dump(out, open(DIR + "/out/dense_supports.pkl", "wb"))
