"""Row-approach profile: greedy chain of subcodes W_k; F(W)=free row-data dims mod gauge, P(W)=pruning bits."""
import sys, math
sys.path.insert(0, "<HOME>/c72_indep/src")
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[0])
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[1].split("R = Basis()")[0])
gauge = []
for i in range(n):
    M = 0
    for a in range(18):
        for b in range(a, 18):
            if (G[a] >> i & 1) and (G[b] >> i & 1):
                M |= 1 << FS.idx[a][b]
    gauge.append(M)
lowset = set(low)
def F_of(Phi):
    # Phi: Basis of functionals (fully reduced)
    vecs = list(Phi.B.values())
    d = len(vecs)
    D = Basis()
    for f in diag: D.add(f)
    PD = Basis(); PD.B = dict(Phi.B)
    for f in diag: PD.add(f)
    inter = d + 17 - len(PD.B)
    # gauge rank: matrix rows f, cols i
    rows = []
    for f in vecs:
        r = 0
        for i, Mi in enumerate(gauge):
            if wt(f & Mi) & 1: r |= 1 << i
        rows.append(r)
    g = rank(rows, 36)
    return d - inter - g
def run(first, cand_weights=(8,), maxk=18):
    Wb = []
    Wwords = [0]
    Phi = Basis()
    P = 0.0
    for k in range(maxk):
        best = None
        cands = [first] if k == 0 else [y for y in low if wt(y) in cand_weights]
        Wset = set(Wwords)
        for b in cands:
            if b in Wset: continue
            newP = sum(logfrac[z] for z in (b ^ w for w in Wwords) if z in lowset)
            # dims added
            tmp = Basis(); tmp.B = dict(Phi.B)
            for g_ in G: tmp.add(FS.functional(b, g_))
            Fn = F_of(tmp)
            score = Fn + P + newP
            if best is None or score < best[0]:
                best = (score, b, tmp, Fn, newP)
        score, b, Phi, Fn, newP = best
        P += newP
        Wb.append(b)
        Wwords = Wwords + [b ^ w for w in Wwords]
        cnt = Counter(wt(z) for z in Wwords if z in lowset)
        print(f"k={k+1:2d} wt(b)={wt(b)} F={Fn:3d} P={-P:6.2f} est={score:6.2f}  low words in W: w8={cnt[8]} w10={cnt[10]} w12={cnt[12]}", flush=True)
W8 = [y for y in low if wt(y) == 8]
run(W8[0], (8,), 13)
