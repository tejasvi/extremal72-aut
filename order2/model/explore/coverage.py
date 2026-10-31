"""For a flag of code CI: for each level t and each low word u in W_t, the coverage fraction |O(u) cap W_t|/|O(u)|
(= fraction of g in Aut(Y) whose image of u is determined at level t).  Prints, per level, the best few u
(weight, orbit size, level where u enters, coverage).  Usage: coverage.py CI FLAGFILE TMAX"""
import sys, pickle
sys.path.insert(0, '<HOME>/c72/explore/src')
from common import *
ci = int(sys.argv[1]); flag = [int(x) for x in open(sys.argv[2]).read().split()[1:]]; TMAX = int(sys.argv[3])
codes = load(); Yg = codes[ci]
res = pickle.load(open('<HOME>/c72/c2par/invs.pkl', 'rb'))
gens = res[ci]['perms']
def ap(perm, w):
    o = 0
    while w:
        b = w & -w; i = b.bit_length() - 1; o |= 1 << perm[i]; w ^= b
    return o
low = set(int(l.split()[0]) for l in open(f'<HOME>/c72/explore/data/low_{ci}.txt'))
orb_of = {}
for y in low:
    if y in orb_of: continue
    orb = {y}; fr = [y]
    while fr:
        nf = []
        for v in fr:
            for g in gens:
                x = ap(g, v)
                if x not in orb: orb.add(x); nf.append(x)
        fr = nf
    fo = frozenset(orb)
    for x in orb: orb_of[x] = fo
span = [0]; enter = {}
for t in range(TMAX):
    b = flag[t]; new = [s ^ b for s in span]; span += new
    for v in new:
        if v in low: enter[v] = t + 1
    S = set(span)
    best = {}
    for u in enter:
        O = orb_of[u]; cov = sum(1 for x in O if x in S) / len(O)
        key = (pc(u), len(O))
        if key not in best or cov > best[key][0]: best[key] = (cov, enter[u])
    top = sorted(best.items(), key=lambda kv: -kv[1][0])[:5]
    print(f"t={t+1}: " + "; ".join(f"w{k[0]} orb{k[1]} cov {v[0]:.3f} (in at {v[1]})" for k, v in top))
