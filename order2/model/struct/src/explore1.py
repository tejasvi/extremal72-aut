import sys, math, random, time
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import *
t0 = time.time()
I = read_inst(sys.argv[1])
cons = I['cons']; N = I['N']
print('N', N, 'NC', len(cons), 'read', round(time.time()-t0, 1), 's')
byy = {}
for c in cons:
    p, nr, nb, nrel = pass_prob(c); c['p'] = p; c['L'] = -math.log2(p)
    byy[c['y']] = c
from collections import Counter
print('weights', Counter(c['wt'] for c in cons))
for w in (8, 10, 12):
    Ls = [c['L'] for c in cons if c['wt'] == w]; ms = Counter((c['m'], len(relations(c['forms']))) for c in cons if c['wt'] == w)
    print(w, 'mean L', sum(Ls)/len(Ls), 'min', min(Ls), 'max', max(Ls), 'm/rel', ms)
def rk(vs):
    b = Basis()
    for v in vs: b.add(v)
    return len(b)
w8 = [c for c in cons if c['wt'] == 8]
pc = lambda x: bin(x).count('1')
stats = Counter()
random.seed(1)
for _ in range(3000):
    a, b = random.sample(w8, 2)
    inter = pc(a['y'] & b['y'])
    s = a['y'] ^ b['y']
    r2 = rk(a['forms'] + b['forms'])
    extra = []
    if s in byy: extra = byy[s]['forms']
    r3 = rk(a['forms'] + b['forms'] + extra)
    stats[(inter, s in byy, r2, r3)] += 1
for k, v in sorted(stats.items()): print(k, v)
