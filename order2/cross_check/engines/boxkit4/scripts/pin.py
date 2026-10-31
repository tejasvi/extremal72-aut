"""Make a sub-instance of an lwe instance file: pin all variables of levels < L to the prefix X0 (variables are
numbered by level, so these are variables 0 .. vstart[L]-1) and renumber the rest.  Levels and constraint order are
kept, so the sub-instance's search is exactly the subtree of the original search below the node X0|_{<L}.
Optional relaxations of the bad sets (to create solutions):
  --plant HEXFULL     remove from every constraint the syndrome attained by the full assignment HEXFULL
  --keep Q SEED       keep each bad syndrome independently with probability Q
  --addbad K SEED     add K random syndromes to every bad set of level >= L (gives method-1 constraints,
                      i.e. the weight-14 ones whose real bad set {0} is unreachable, something to remove)
Usage: pin.py INSTANCE OUT L PREFIXHEX [--plant HEX] [--keep Q SEED]"""
import sys, random


def par(x): return x.bit_count() & 1


def main():
    inst, out, L, x0 = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4], 16)
    plant = int(sys.argv[sys.argv.index('--plant') + 1], 16) if '--plant' in sys.argv else None
    addbad = None
    if '--addbad' in sys.argv:
        i = sys.argv.index('--addbad'); addbad = (int(sys.argv[i + 1]), random.Random(int(sys.argv[i + 2])))
    keep = None
    if '--keep' in sys.argv:
        i = sys.argv.index('--keep'); keep = (float(sys.argv[i + 1]), random.Random(int(sys.argv[i + 2])))
    lines = open(inst).read().split('\n')
    N, NLEV, NC = map(int, lines[0].split()); vs = list(map(int, lines[1].split()))
    P = vs[L]; pmask = (1 << P) - 1
    x0 &= pmask
    if plant is not None: assert plant & pmask == x0, 'planted assignment must extend the prefix'
    o = [f'{N - P} {NLEV} {NC}', ' '.join(str(max(0, v - P)) for v in vs)]
    pos = 2
    for c in range(NC):
        lv, wt, m, nb = map(int, lines[pos].split()); pos += 1
        forms = []
        for s in range(m):
            hx, cc = lines[pos].split(); pos += 1
            forms.append((int(hx, 16), int(cc)))
        bad = list(map(int, lines[pos].split())) if nb else []; pos += 1
        if nb == 0: assert lines[pos - 1].strip() == ''
        nf = [((vm >> P), cc ^ par(vm & x0)) for (vm, cc) in forms]
        if plant is not None and lv >= L:
            s = 0
            for k, (vm, cc) in enumerate(forms): s |= (par(vm & plant) ^ cc) << k
            bad = [b for b in bad if b != s]
        if keep is not None and lv >= L:
            bad = [b for b in bad if keep[1].random() < keep[0]]
        if addbad is not None and lv >= L:
            bad = sorted(set(bad) | {addbad[1].randrange(1 << m) for _ in range(addbad[0])})
        o.append(f'{lv} {wt} {m} {len(bad)}')
        for (vm, cc) in nf: o.append(f'{vm:x} {cc}')
        o.append(' '.join(map(str, bad)))
    open(out, 'w').write('\n'.join(o) + '\n')


if __name__ == '__main__':
    main()
