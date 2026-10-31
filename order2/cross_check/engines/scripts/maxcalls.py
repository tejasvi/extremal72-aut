"""Upper bound on lh_reject calls (symmetry tests) per process for lwe8-run part logs: nodes at levels t with
t-1 >= level of the key constraint, plus leaves (t = NLEV).  Prints the maximum per directory.  Audit code.
Usage: maxcalls.py KEYLEVEL DIR..."""
import sys, glob, os
lv0 = int(sys.argv[1])
for d in sys.argv[2:]:
    mx = (0, None); n = 0
    for f in glob.glob(os.path.join(d, 'p*.log')):
        tot = 0; leaves = 0
        for l in open(f):
            if l.startswith('LEVEL '):
                p = l.split(); t = int(p[1]); nodes = int(p[7]); kids = int(p[9])
                if t - 1 >= lv0: tot += nodes
                if t == 17: leaves = kids
        tot += leaves; n += 1
        if tot > mx[0]: mx = (tot, os.path.basename(f))
    print(f'{d}: parts {n}, max symmetry-test calls per process <= {mx[0]:.4e} ({mx[1]}), 2^32 = {2**32:.4e}, ratio {mx[0] / 2**32:.3f}')
