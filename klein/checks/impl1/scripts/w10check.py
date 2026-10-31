"""Are the weight-10 constraints without a reachable bad syndrome exactly those of beta-fixed words?"""
import sys, pickle, glob, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE + '/../../../model'); sys.path.insert(0, HERE + '/../scripts')
from indep_check import parse_instance, apply_perm
tot = collections.Counter()
for line in open(HERE + '/../../../model/lw_all_list.txt'):
    ci, ri = line.split()
    inst = f'{HERE}/../../../impl1_runs/lwinst/lwf_{ci}_{ri}.txt'
    N, NL, vs, cons = parse_instance(inst)
    MP = pickle.load(open(f'{HERE}/../chk/map_{ci}_{ri}.pkl', 'rb')); beta = MP['beta']; cmap = MP['cmap']
    for idx, (lv, wt, forms, bad) in enumerate(cons):
        if wt != 10: continue
        c0 = sum(cc << s for s, (vm, cc) in enumerate(forms)); piv = {}
        for v in range(N):
            col = sum(((vm >> v) & 1) << s for s, (vm, cc) in enumerate(forms))
            for b, r in piv.items():
                if (col >> b) & 1: col ^= r
            if col:
                hb = col.bit_length() - 1
                for b2 in list(piv):
                    if (piv[b2] >> hb) & 1: piv[b2] ^= col
                piv[hb] = col
        def insp(x):
            for b, r in piv.items():
                if (x >> b) & 1: x ^= r
            return x == 0
        reach = any(insp(b ^ c0) for b in bad)
        ys = cmap[idx]; fixed = all(apply_perm(beta, y) == y for y in ys)
        tot[(reach, fixed)] += 1
print({f'reachable={k[0]} betafixed={k[1]}': v for k, v in sorted(tot.items())})
