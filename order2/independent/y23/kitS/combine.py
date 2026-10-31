#!/usr/bin/env python3
"""Combine joinsplit outputs into plain-join J lines.
usage: combine.py OUT_J_FILE JS_FILE... [--ref REF_J_FILE]
JS x ok n1 n2 npair npass nodes_p1 nodes_pairs nodes2 nsol NSPLIT SPLIT  (13 fields)
For each x: exactly one line per SPLIT 0..NSPLIT-1 (same NSPLIT); ok, n1, n2, nodes_p1, nodes2 equal in all splits.
Combined: J x ok n1 n2 sum(npair) sum(npass) nodes_p1+sum(nodes_pairs) nodes2 sum(nsol)."""
import sys
args = sys.argv[1:]
ref = None
if '--ref' in args:
    k = args.index('--ref'); ref = args[k + 1]; args = args[:k] + args[k + 2:]
out, files = args[0], args[1:]
g = {}; nsolline = 0; bad = 0
for fn in files:
    for l in open(fn):
        f = l.split()
        if not f: continue
        if f[0] == 'SOL': nsolline += 1; continue
        if f[0] != 'JS': continue
        if len(f) != 13: print('INCOMPLETE', fn, l.strip()); bad += 1; continue
        g.setdefault(f[1], []).append(f)
res = {}
for x, L in g.items():
    ns = {int(f[11]) for f in L}
    if len(ns) != 1: print('MIXED NSPLIT', x); bad += 1; continue
    n = ns.pop()
    ks = sorted(int(f[12]) for f in L)
    if ks != list(range(n)): print('SPLITS', x, 'have', ks[:10], 'of', n); bad += 1; continue
    inv = {(f[2], f[3], f[4], f[7], f[9]) for f in L}
    if len(inv) != 1: print('SPLIT-INVARIANT FIELDS DIFFER', x, inv); bad += 1; continue
    ok, n1, n2, p1, nodes2 = inv.pop()
    npair = sum(int(f[5]) for f in L); npass = sum(int(f[6]) for f in L)
    nodes = int(p1) + sum(int(f[8]) for f in L); nsol = sum(int(f[10]) for f in L)
    res[x] = f'J {x} {ok} {n1} {n2} {npair} {npass} {nodes} {nodes2} {nsol}'
with open(out, 'w') as o:
    for x in sorted(res): o.write(res[x] + '\n')
print(f'combined {len(res)} reps, problems {bad}, SOL lines {nsolline}')
if ref:
    R = {}
    for l in open(ref):
        f = l.split()
        if f and f[0] == 'J' and len(f) == 10: R[f[1]] = ' '.join(f)
    same = sum(1 for x in R if res.get(x) == R[x])
    diff = [x for x in R if x in res and res[x] != R[x]]
    miss = [x for x in R if x not in res]
    print(f'reference {len(R)}: identical {same}, different {len(diff)}, missing {len(miss)}')
    for x in diff[:20]: print('REF', R[x]); print('NEW', res[x])
