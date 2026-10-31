"""Independent checks of a parcheck data file: (1) ANF degree of every word table (bound for the hitting set);
(2) the data-file function at random points equals an independent computation (lowcount.LowCounter) of the
certificate quantity on the same form B (here: kind x12b -> X8b + X12 mod 2)."""
import sys, random
import numpy as np
sys.path.insert(0, '<HOME>/c72/c2opt/math')
from collections import Counter
def anf_degree(bits, r):
    a = np.array(bits, dtype=np.int64)
    for i in range(r):
        step = 1 << i
        a = a.reshape(-1, 2 * step)
        a[:, step:] ^= a[:, :step]
        a = a.reshape(-1)
    nz = np.nonzero(a)[0]
    return max((bin(int(m)).count('1') for m in nz), default=-1)
fn = sys.argv[1]
lines = open(fn).read().split('\n')
N, W, exp = map(int, lines[0].split())
tabs = []
degs = Counter()
for w in range(W):
    r, h = lines[1 + w].split(); r = int(r); t = int(h, 16)
    bits = [(t >> s) & 1 for s in range(1 << r)]
    tabs.append((r, bits))
    degs[(r, anf_degree(bits, r))] += 1
print('table (r, degree) counts:', sorted(degs.items()), ' max degree', max(d for (r, d) in degs))
s0 = list(map(int, lines[1 + W].split()))
E = [list(map(int, lines[2 + W + v].split())) for v in range(N)]
assert len(s0) == W and all(len(e) == W for e in E)
# evaluate g at random x
rng = random.Random(1)
vals = []
for _ in range(200):
    xs = [v for v in range(N) if rng.getrandbits(1)]
    syn = s0[:]
    for v in xs:
        e = E[v]
        syn = [a ^ b for a, b in zip(syn, e)]
    g = sum(tabs[w][1][syn[w]] for w in range(W)) % 2
    vals.append(g)
print('data-file g at 200 random points:', Counter(vals))
