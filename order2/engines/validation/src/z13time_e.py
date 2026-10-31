"""z13time_e.py RAWFILE... : paired timing verdict rc11 vs rc13 variants from 'tag_engine_cCPU user real' lines.
Tail time = part user time minus the mean prefix-only time of the same package and engine (same round/file)."""
import sys, re, collections
W = {'y0': 0.39, 'y14': 0.34, 'y19b': 0.09, 'y26f': 0.19}   # share of rc11 core-hours (part time x NPART, fleet04 rounds)
for fn in sys.argv[1:]:
    T = collections.defaultdict(list); P = collections.defaultdict(list)
    for l in open(fn):
        m = re.match(r'^(y\w+?)_(p\d+|pfx\w+)_(lwe11\w+)_c(\d+) ([\d.]+) ([\d.]+)$', l.strip())
        if not m: continue
        pk, part, eng, cpu, u = m.group(1), m.group(2), m.group(3), m.group(4), float(m.group(5))
        (P if part.startswith('pfx') else T)[(pk, part if not part.startswith('pfx') else 'pfx', eng)].append(u)
    print(f'== {fn}')
    gains = collections.defaultdict(list)
    for (pk, part, eng), v in sorted(T.items()):
        if eng == 'lwe11rc11': continue
        base = T.get((pk, part, 'lwe11rc11'))
        if not base: continue
        pb = P.get((pk, 'pfx', 'lwe11rc11')); pe = P.get((pk, 'pfx', eng)) or pb
        b = sum(base) / len(base); e = sum(v) / len(v)
        bt = b - (sum(pb) / len(pb) if pb else 0); et = e - (sum(pe) / len(pe) if pe else 0)
        g = 100 * (1 - e / b); gt = 100 * (1 - et / bt)
        gains[(pk, eng)].append(gt)
        print(f'{pk:5s} {part:6s} {eng:11s} rc11 {b:7.2f} eng {e:7.2f} gain {g:5.1f}%  tail {bt:7.2f} -> {et:7.2f} gain {gt:5.1f}%')
    for eng in sorted({e for _, e in gains}):
        per = {pk: sum(gains[(pk, eng)]) / len(gains[(pk, eng)]) for pk in W if (pk, eng) in gains}
        if len(per) == 4:
            print(f'{eng}: tail gains ' + ', '.join(f'{pk} {g:.1f}%' for pk, g in per.items()) + f'; weighted {sum(W[pk] * per[pk] for pk in W):.2f}%')
        else:
            print(f'{eng}: tail gains ' + ', '.join(f'{pk} {g:.1f}%' for pk, g in per.items()))
