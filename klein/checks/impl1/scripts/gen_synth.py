"""Synthetic lwe instances with N > 64 (exercises the 128-bit masks of lwe and the high word of naive's parser):
NLEV levels of KT variables, NC constraints per level, random forms over the variables of levels <= t (always
using some level-t variable), random bad sets of density DEN, plus a planted solution.
Usage: gen_synth.py OUT NLEV KT NC DEN SEED"""
import sys, random
out, NLEV, KT, NC, DEN, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6])
rnd = random.Random(seed)
N = NLEV * KT
vs = [t * KT for t in range(NLEV + 1)]
X1 = rnd.getrandbits(N)
def par(x): return bin(x).count('1') & 1
lines = []; cons = []
for t in range(NLEV):
    for c in range(NC):
        m = rnd.randint(2, 10)
        forms = []
        for s in range(m):
            vm = rnd.getrandbits(vs[t + 1]) | (1 << rnd.randrange(vs[t], vs[t + 1]))
            forms.append((vm, rnd.getrandbits(1)))
        s1 = sum((par(vm & X1) ^ cc) << s for s, (vm, cc) in enumerate(forms))
        bad = sorted(b for b in range(1 << m) if b != s1 and rnd.random() < DEN)
        cons.append((t, forms, bad))
lines.append(f'{N} {NLEV} {len(cons)}'); lines.append(' '.join(map(str, vs)))
for (t, forms, bad) in cons:
    lines.append(f'{t} 0 {len(forms)} {len(bad)}')
    for (vm, cc) in forms: lines.append(f'{vm:x} {cc}')
    lines.append(' '.join(map(str, bad)))
open(out, 'w').write('\n'.join(lines) + '\n')
print(f'{X1:032x}')
