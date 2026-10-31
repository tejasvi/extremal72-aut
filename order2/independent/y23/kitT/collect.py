#!/usr/bin/env python3
"""collect.py: combine out/*.out JT lines per rep. For each rep: exactly NSPLIT items 0..NSPLIT-1 (same NSPLIT),
split-invariant fields (ok n1 n1kept n2 nodes_p1 nodes2 nh ns) equal; sums of npair npass nodes_pairs nsol.
Prints one combined line per rep: JTC x ok n1 n1kept n2 npair npass nodes nodes2 nsol nh ns, and all SOL lines."""
import glob, sys
g = {}; sol = []
for fn in sorted(glob.glob('out/*.out')):
    for l in open(fn):
        f = l.split()
        if f and f[0] == 'SOL': sol.append((fn, l.strip()))
        if f and f[0] == 'JT':
            assert len(f) == 16, fn
            g.setdefault(f[1], []).append(f)
for x, L in sorted(g.items()):
    ns = {f[12] for f in L}; assert len(ns) == 1, x
    n = int(ns.pop()); ks = sorted(int(f[13]) for f in L)
    inv = {(f[2], f[3], f[4], f[5], f[8], f[10], f[14], f[15]) for f in L}
    if ks != list(range(n)) or len(inv) != 1:
        print('INCOMPLETE', x, len(ks), 'of', n, 'invariant sets', len(inv)); continue
    ok, n1, n1k, n2, p1, nodes2, nh, nsw = inv.pop()
    s = lambda c: sum(int(f[c]) for f in L)
    print('JTC %s %s %s %s %s %d %d %d %s %d %s %s' % (x, ok, n1, n1k, n2, s(6), s(7), int(p1) + s(9), nodes2, s(11), nh, nsw))
for fn, l in sol: print('SOL', fn, l)
print('SOL lines:', len(sol))
