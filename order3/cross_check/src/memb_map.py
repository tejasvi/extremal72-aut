# map dumped sample invariants to cls24 line indices (via own per-shard invariant files)
import numpy as np, sys
S = '../scan/'
NS = 6
arrs = [np.fromfile(S + f'full_{k}.inv', dtype=np.uint64) for k in range(NS)]
n = sum(len(a) for a in arrs); inv = np.empty(n, dtype=np.uint64)
for k in range(NS): inv[k::NS] = arrs[k]
order = np.argsort(inv); sv = inv[order]
out = open(sys.argv[2], 'w'); nf = 0
for line in open(sys.argv[1]):
    h = np.uint64(int(line.split('inv=')[1], 16))
    j = np.searchsorted(sv, h)
    if j < n and sv[j] == h: out.write('%d\n' % order[j]); nf += 1
    else: out.write('-1\n')
print('mapped', nf)
