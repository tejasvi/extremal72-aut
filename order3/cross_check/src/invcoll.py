import numpy as np, sys
NS = 6
arrs = [np.fromfile(f'full_{k}.inv', dtype=np.uint64) for k in range(NS)]
n = sum(len(a) for a in arrs)
inv = np.empty(n, dtype=np.uint64)
for k in range(NS):
    inv[k::NS] = arrs[k]          # line idx = NS*p + k
print('lines', n, 'zeros', int((inv == 0).sum()))
order = np.argsort(inv, kind='stable')
s = inv[order]
dup = np.nonzero(s[1:] == s[:-1])[0]
print('equal adjacent pairs', len(dup))
groups = {}
for d in dup:
    groups.setdefault(int(s[d]), set()).update([int(order[d]), int(order[d+1])])
print('collision groups', len(groups))
with open('inv_collisions.txt', 'w') as f:
    for h, idxs in groups.items():
        f.write('%016x %s\n' % (h, ' '.join(map(str, sorted(idxs)))))
np.save('inv_sorted_vals.npy', s)
