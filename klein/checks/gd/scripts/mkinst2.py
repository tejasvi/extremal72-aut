"""Like mkinst.py, but additionally writes OUT.pin.txt: the ORIGINAL (uncompressed, full-width) forms with the same
augmented good sets, plus one unit word (d=1, mask = 1<<t, good = {value}) per fixed variable t.  The solver on the
pinned file works with the original variable numbering (exercises bits >= 64 for wide instances).
usage: mkinst2.py IN OUT SEED NFIX NPLANT RELAX FLIPS"""
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
# make sure the high bits (>= 64) are free when the instance is wide, so the search branches on them
cand = [t for t in range(nW) if t < 64]
F = rng.sample(cand, nfix); Fm = sum(1 << t for t in F)
free = [t for t in range(nW) if t not in F]
planted = [w0]
while len(planted) < nplant:
    if flips > 0:
        w = planted[rng.randrange(len(planted))]
        for t in rng.sample(free, min(flips, len(free))): w ^= 1 << t
    else:
        w = (w0 & Fm) | (rng.getrandbits(nW) & ~Fm)
    if w not in planted: planted.append(w)
def compress(m):
    r = 0
    for k, t in enumerate(free):
        if (m >> t) & 1: r |= 1 << k
    return r
L1 = [f'{len(free)} {len(words)}']; L2 = [f'{nW} {len(words) + len(F)}']
for wt, d, forms, good in words:
    g2 = set(good)
    for w in planted: g2.add(cls(forms, w))
    if relax > 0:
        for g in range(1 << d):
            if g not in g2 and rng.random() < relax: g2.add(g)
    gl = ' '.join(map(str, sorted(g2)))
    L1.append(f'{wt} {d} {len(g2)}'); L2.append(f'{wt} {d} {len(g2)}')
    for (m, c) in forms:
        L1.append(f'{compress(m & ~Fm):x} {c ^ (pc(m & Fm & w0) & 1)}'); L2.append(f'{m:x} {c}')
    L1.append(gl); L2.append(gl)
for t in sorted(F):
    L2.append(f'14 1 1'); L2.append(f'{1 << t:x} 0'); L2.append(f'{(w0 >> t) & 1}')
open(out, 'w').write('\n'.join(L1) + '\n')
open(out + '.pin.txt', 'w').write('\n'.join(L2) + '\n')
open(out + '.planted', 'w').write('\n'.join(f'{compress(w):x}' for w in planted) + '\n')
open(out + '.free', 'w').write(' '.join(map(str, free)) + '\n')
