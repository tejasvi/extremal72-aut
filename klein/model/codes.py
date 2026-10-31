"""Exact pair-count tables N[(i,j,t)] for the Golay code (n=24) and the extended QR code QR48 (n=48).
Used only to validate the formulation: every constraint must hold exactly at these codes."""
import sys, time, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
import numpy as np

def span_np(gens):
    W = np.zeros(1, dtype=np.uint64)
    for g in gens:
        W = np.concatenate([W, W ^ np.uint64(g)])
    return W

def gf2_rank(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis), basis

def golay_gens():
    g = sum(1 << e for e in (11, 10, 6, 5, 4, 2, 0))
    gens = []
    for s in range(12):
        w = g << s
        gens.append(w | ((bin(w).count('1') & 1) << 23))
    return gens

def qr48_gens():
    p = 47
    Q = sorted({(x * x) % p for x in range(1, p)})
    cands = []
    for base in (Q, sorted(set(range(1, p)) - set(Q))):
        for add0 in (0, 1):
            e = sum(1 << r for r in base) | add0
            shifts = [((e << s) | (e >> (p - s))) & ((1 << p) - 1) for s in range(p)]
            rk, basis = gf2_rank(shifts)
            if rk == 24:
                gens = [b | ((bin(b).count('1') & 1) << p) for b in basis]
                cands.append(gens)
    for gens in cands:
        rk, basis = gf2_rank(gens)
        # doubly-even + self-orthogonal check on basis
        ok = all(bin(b).count('1') % 4 == 0 for b in basis) and all(bin(a & b).count('1') % 2 == 0 for a in basis for b in basis)
        if ok:
            return basis
    raise RuntimeError("no QR48")

def apply_perm(W, perm):
    out = np.zeros_like(W)
    for i, pi in enumerate(perm):
        out |= ((W >> np.uint64(i)) & np.uint64(1)) << np.uint64(pi)
    return out

def psl2_47_perms():
    p = 47; INF = 47
    g = next(r for r in range(2, p) if len({pow(r, k, p) for k in range(1, p)}) == p - 1)
    s = [((x + 1) % p) for x in range(p)] + [INF]
    m = [((g * g * x) % p) for x in range(p)] + [INF]
    inv = [INF if x == 0 else ((-pow(x, p - 2, p)) % p) for x in range(p)] + [0]
    return [s, m, inv]

def counts_by_orbits(W, n, perms):
    """W: all codewords (uint64). perms: generators of a subgroup of Aut(C). Returns N dict."""
    Ws = np.sort(W)
    N = len(Ws)
    idxs = []
    for P in perms:
        img = apply_perm(Ws, P)
        idx = np.searchsorted(Ws, img)
        assert np.all(Ws[np.minimum(idx, N - 1)] == img), "perm does not preserve code"
        idxs.append(idx)
        inv = np.empty_like(idx); inv[idx] = np.arange(N)
        idxs.append(inv)
    label = np.arange(N)
    it = 0
    while True:
        old = label.copy()
        for idx in idxs:
            label = np.minimum(label, label[idx])
        label = np.minimum(label, label[label])
        it += 1
        if np.array_equal(old, label):
            break
    reps, sizes = np.unique(label, return_counts=True)
    print(f"orbits: {len(reps)} after {it} iterations", flush=True)
    wts = np.bitwise_count(Ws).astype(np.int64)
    Nt = {}
    tab = np.zeros((n + 1, n + 1, n + 1), dtype=object)  # [i][j][t]
    for r, sz in zip(reps, sizes):
        v = Ws[r]
        i = int(wts[r])
        a = np.bitwise_count(Ws & v).astype(np.int64)
        cnt = np.bincount(a * (n + 1) + wts, minlength=(n + 1) ** 2).reshape(n + 1, n + 1)  # [t][j]
        for t, j in zip(*np.nonzero(cnt)):
            key = (i, int(j), int(t))
            Nt[key] = Nt.get(key, 0) + int(sz) * int(cnt[t, j])
    return Nt

def counts_direct(W, n):
    wts = np.bitwise_count(W).astype(np.int64)
    Nt = {}
    for v, i in zip(W, wts):
        a = np.bitwise_count(W & v).astype(np.int64)
        cnt = np.bincount(a * (n + 1) + wts, minlength=(n + 1) ** 2).reshape(n + 1, n + 1)
        for t, j in zip(*np.nonzero(cnt)):
            key = (int(i), int(j), int(t))
            Nt[key] = Nt.get(key, 0) + int(cnt[t, j])
    return Nt

if __name__ == "__main__":
    out = HERE + "/data"
    t0 = time.time()
    W = span_np(golay_gens())
    assert len(np.unique(W)) == 4096
    N24 = counts_direct(W, 24)
    pickle.dump(N24, open(f"{out}/N24_golay.pkl", "wb"))
    print("golay done", len(N24), time.time() - t0, flush=True)
    b = qr48_gens()
    W = span_np(b)
    wd = np.bincount(np.bitwise_count(W), minlength=49)
    print("QR48 weight distribution:", {k: int(v) for k, v in enumerate(wd) if v}, flush=True)
    N48 = counts_by_orbits(W, 48, psl2_47_perms())
    pickle.dump(N48, open(f"{out}/N48_qr.pkl", "wb"))
    print("qr48 done", len(N48), time.time() - t0, flush=True)
