#!/usr/bin/env python3
"""jt2j.py OUT JT_FILE... [--ref REF]: combine JT lines (engine12/13 joinstab, any NSPLIT) of UNREDUCED runs
(STABFILE "-", so |S1 kept| = |S1|, nh = ns = 0) into plain-join J lines
J x ok n1 n2 sum(npair) sum(npass) nodes_p1+sum(nodes_pairs) nodes2 sum(nsol); compare with REF J lines."""
import sys
args = sys.argv[1:]; ref = None
if '--ref' in args:
    k = args.index('--ref'); ref = args[k + 1]; args = args[:k] + args[k + 2:]
out, files = args[0], args[1:]
g = {}; bad = 0
for fn in files:
    for l in open(fn):
        f = l.split()
        if f and f[0] == 'JT':
            if len(f) != 16: print('INCOMPLETE', l.strip()); bad += 1; continue
            g.setdefault(f[1], []).append(f)
res = {}
for x, L in g.items():
    n = {int(f[12]) for f in L}
    if len(n) != 1: print('MIXED', x); bad += 1; continue
    n = n.pop()
    if sorted(int(f[13]) for f in L) != list(range(n)): print('SPLITS', x); bad += 1; continue
    inv = {(f[2], f[3], f[4], f[5], f[8], f[10], f[14], f[15]) for f in L}
    if len(inv) != 1: print('INVARIANTS', x, inv); bad += 1; continue
    ok, n1, n1k, n2, p1, nodes2, nh, ns = inv.pop()
    if n1k != n1 or nh != '0' or ns != '0': print('NOT UNREDUCED', x); bad += 1; continue
    s = lambda c: sum(int(f[c]) for f in L)
    res[x] = 'J %s %s %s %s %d %d %d %s %d' % (x, ok, n1, n2, s(6), s(7), int(p1) + s(9), nodes2, s(11))
open(out, 'w').write(''.join(res[x] + '\n' for x in sorted(res)))
print('combined %d, problems %d' % (len(res), bad))
if ref:
    R = {}
    for l in open(ref):
        f = l.split()
        if f and f[0] == 'J' and len(f) == 10: R[f[1]] = ' '.join(f)
    same = sum(res.get(x) == R[x] for x in R)
    print('reference %d: identical %d, different %d, missing %d' % (len(R), same, sum(x in res and res[x] != R[x] for x in R), sum(x not in res for x in R)))
    for x in R:
        if x in res and res[x] != R[x]: print('REF', R[x]); print('NEW', res[x])
