"""Make a test sub-instance: fix nfix random variables to the values of a random planted solution w0, plant
nplant solutions (w0 and variants agreeing on the fixed variables), optionally relax good sets.
usage: mkinst.py IN OUT SEED NFIX NPLANT RELAX FLIPS  -> writes OUT and OUT.planted (reduced coordinates)"""
import sys, random
def pc(x): return bin(x).count('1')
def parse(fn):
    L = open(fn).read().split('\n'); nW, nw = map(int, L[0].split()); p = 1; words = []
    for _ in range(nw):
        wt, d, ng = map(int, L[p].split()); p += 1; forms = []
        for t in range(d):
            m, c = L[p].split(); p += 1; forms.append((int(m, 16), int(c)))
        good = set(map(int, L[p].split())) if ng else set(); p += 1
        words.append([wt, d, forms, good])
    return nW, words
def cls(forms, w):
    g = 0
    for t, (m, c) in enumerate(forms): g |= ((pc(m & w) & 1) ^ c) << t
    return g
inp, out, seed, nfix, nplant, relax, flips = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7])
rng = random.Random(seed)
nW, words = parse(inp)
w0 = rng.getrandbits(nW)
F = rng.sample(range(nW), nfix); Fm = sum(1 << t for t in F)
free = [t for t in range(nW) if t not in F]
planted = [w0]
while len(planted) < nplant:
    w = planted[rng.randrange(len(planted))] if flips > 0 else w0
    if flips > 0:
        for t in rng.sample(free, min(flips, len(free))): w ^= 1 << t
    else:
        w = (w0 & Fm) | (rng.getrandbits(nW) & ~Fm)
    if w not in planted: planted.append(w)
def compress(m):
    r = 0
    for k, t in enumerate(free):
        if (m >> t) & 1: r |= 1 << k
    return r
lines = [f'{len(free)} {len(words)}']
for wt, d, forms, good in words:
    g2 = set(good)
    for w in planted: g2.add(cls(forms, w))
    if relax > 0:
        for g in range(1 << d):
            if g not in g2 and rng.random() < relax: g2.add(g)
    lines.append(f'{wt} {d} {len(g2)}')
    for (m, c) in forms:
        c2 = c ^ (pc(m & Fm & w0) & 1)
        lines.append(f'{compress(m & ~Fm):x} {c2}')
    lines.append(' '.join(map(str, sorted(g2))))
open(out, 'w').write('\n'.join(lines) + '\n')
open(out + '.planted', 'w').write('\n'.join(f'{compress(w):016x}' for w in planted) + '\n')
