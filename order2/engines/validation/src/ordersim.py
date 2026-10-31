# Offline estimate: evaluations per node for the current lane order vs greedy orders trained on half of the sampled nodes.
import sys, numpy as np
fn, nc, nbytes = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
raw = np.fromfile(fn, dtype=np.uint8)
nn = raw.size // (nc * nbytes)
X = raw[:nn * nc * nbytes].reshape(nn, nc, nbytes)
pad = (-nbytes) % 8
if pad: X = np.concatenate([X, np.zeros((nn, nc, pad), np.uint8)], axis=2)
W = X.view(np.uint64).reshape(nn, nc, -1)          # bad bitmaps
kt_bits = nbytes * 8
allm = np.zeros(W.shape[2], np.uint64)
for v in range(min(kt_bits, 64 * W.shape[2])): allm[v >> 6] |= np.uint64(1 << (v & 63))
def popc(a):
    return np.bitwise_count(a).sum(axis=-1).astype(np.int64)
def cost(order, idx):
    alive = np.broadcast_to(allm, (len(idx), W.shape[2])).copy()
    done = np.zeros(len(idx), bool); ev = np.zeros(len(idx), np.int64)
    for k, ln in enumerate(order):
        ev[~done] += 1
        alive &= ~W[idx, ln]
        done |= ~alive.any(axis=1)
    return ev.mean(), (~done).mean()
def greedy(idx, mode):
    alive = np.broadcast_to(allm, (len(idx), W.shape[2])).copy(); rem = list(range(nc)); order = []
    while rem:
        act = alive.any(axis=1)
        if not act.any(): order += rem; break
        a = alive[act]; cnt = popc(a)
        best = None
        for ln in rem:
            nw = a & ~W[idx[act], ln]; c2 = popc(nw)
            if mode == 'kill': sc = (cnt - c2).sum()
            elif mode == 'frac': sc = ((cnt - c2) / cnt).sum()
            else: sc = (c2 == 0).sum() * 1e6 + ((cnt - c2) / cnt).sum()
            if best is None or sc > best[0]: best = (sc, ln)
        order.append(best[1]); rem.remove(best[1]); alive &= ~W[idx, best[1]]
    return order
half = nn // 2; tr = np.arange(half); te = np.arange(half, nn)
cur = list(range(nc))
print(f'{fn}: nodes {nn}, lanes {nc}; current order: test evals/node {cost(cur, te)[0]:.2f} (survivor frac {cost(cur, te)[1]:.3f})')
for mode in ('kill', 'frac', 'empty'):
    o = greedy(tr[:4000], mode)
    print(f'  greedy-{mode}: test evals/node {cost(o, te)[0]:.2f}; order head {o[:12]}')
