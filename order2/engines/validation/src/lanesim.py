"""lanesim.py FILE.bin : offline lane-order study on sampled nodes (exp13/lanes.c output).
For each sampled node: per-lane bad bitmaps of the translate+direct lanes in the engine's order.  Evaluates the number
of lanes the filter loop runs until the node's children set is empty, for the current order and for greedy orders built
on one half of the sample and evaluated on the other half."""
import sys, numpy as np
fn = sys.argv[1]
raw = open(fn, 'rb').read()
h = np.frombuffer(raw[:32], dtype=np.int32); t, kt, nr0, ntr, ndir, nc, nb = [int(x) for x in h[:7]]
off = 32; allm = np.frombuffer(raw[off:off + nb], dtype=np.uint8).copy(); off += nb
meta = np.frombuffer(raw[off:off + 16 * nc], dtype=np.int32).reshape(nc, 4); off += 16 * nc
nodes = []; nr0kill = 0
while off < len(raw):
    f = raw[off]; off += 1
    if f == 0: nr0kill += 1; continue
    nodes.append(np.frombuffer(raw[off:off + ntr * nb], dtype=np.uint8).reshape(ntr, nb)); off += ntr * nb
B = np.stack(nodes)                       # (n, ntr, nb)
n = B.shape[0]
nw = max(1, nb // 8)
Bw = B.view(np.uint64).reshape(n, ntr, nw) if nb >= 8 else B.astype(np.uint64)
A = allm.view(np.uint64)[:nw] if nb >= 8 else allm.astype(np.uint64)
ntrans = ntr - ndir
print(f'level {t} kt {kt} lanes: rank0 {nr0} translate {ntrans} direct {ndir} rest {nc - nr0 - ntr}; sampled {n + nr0kill} nodes, {nr0kill} killed by rank-0 lanes')
wts = meta[nr0:nr0 + ntr, 1]; ms = meta[nr0:nr0 + ntr, 2]

def lanes_needed(order, Bx):
    cum = np.bitwise_or.accumulate(Bx[:, order, :], axis=1)        # (n, len(order), nw)
    alive = (A[None, None, :] & ~cum) != 0
    anyalive = alive.any(axis=2)                                    # (n, k)
    dead = ~anyalive
    first = np.where(dead.any(axis=1), dead.argmax(axis=1) + 1, len(order))
    return first, dead.any(axis=1)

def cost(order, Bx, cT=1.0, cD=1.0):
    first, died = lanes_needed(order, Bx)
    isdir = np.array([o >= ntrans for o in order])
    cumc = np.cumsum(np.where(isdir, cD, cT))
    return cumc[first - 1].mean(), first.mean(), died.mean()

cur = list(range(ntr))
rng = np.random.default_rng(1); perm = rng.permutation(n); tr, te = perm[: n // 2], perm[n // 2:]
for cT, cD in [(1.0, 1.0), (1.0, 0.6), (1.0, 1.5)]:
    print(f'-- costs translate {cT} direct {cD}')
    c0, l0, d0 = cost(cur, Bw[te], cT, cD)
    print(f'current order: cost {c0:.2f} lanes {l0:.2f} died-in-lanes {d0:.3f}')
    # greedy: next lane maximizing (nodes killed now + small weight * bits killed) / cost, on the training half
    def greedy(Bx, mode, classes=None):
        m = Bx.shape[0]; alive = np.broadcast_to(A, (m, nw)).copy() & ~np.zeros((m, nw), np.uint64)
        live = np.ones(m, bool); left = list(range(ntr)); order = []
        while left:
            cand = left if classes is None else [o for o in left if (o >= ntrans) == (classes[len(order)] if False else (o >= ntrans))]
            best, bs = None, -1.0
            for o in left:
                if classes == 'T_first' and o >= ntrans and any(x < ntrans for x in left): continue
                na = alive[live] & ~Bx[live, o, :]
                killed_nodes = (~(na != 0).any(axis=1)).sum()
                bits = int(np.bitwise_count(alive[live] & Bx[live, o, :]).sum())
                c = cD if o >= ntrans else cT
                sc = (killed_nodes + (1e-3 if mode == 'nodes' else 1e-1) * bits / max(1, live.sum())) / c if mode != 'bits' else bits / c
                if sc > bs: bs, best = sc, o
            order.append(best); left.remove(best)
            alive[live] &= ~Bx[live, best, :]
            live = live & (alive != 0).any(axis=1)
        return order
    for mode in ['nodes', 'mix', 'bits']:
        for cls in [None, 'T_first']:
            o = greedy(Bw[tr], mode, cls)
            c1, l1, d1 = cost(o, Bw[te], cT, cD)
            print(f'greedy {mode:5s} {"free" if cls is None else "T-first"}: cost {c1:.2f} ({100 * (1 - c1 / c0):+.1f}%) lanes {l1:.2f}  first 12: {o[:12]}')
print('current order weights:', list(wts[:40]))
print('current order m      :', list(ms[:40]))
