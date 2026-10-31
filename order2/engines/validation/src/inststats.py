# Per-level constraint statistics of an lwe instance file (read-only analysis).
import sys
from collections import Counter, defaultdict
def rank_gf2(cols):
    basis = []
    for v in cols:
        for b in basis:
            v = min(v, v ^ b)
        if v: basis.append(v)
    return len(basis)
def main(fn):
    tok = open(fn).read().split()
    p = 0
    def nxt():
        nonlocal p; p += 1; return tok[p - 1]
    N, NLEV, NC = int(nxt()), int(nxt()), int(nxt())
    vs = [int(nxt()) for _ in range(NLEV + 1)]
    per = defaultdict(list)
    for c in range(NC):
        lv, wt, m, nb = int(nxt()), int(nxt()), int(nxt()), int(nxt())
        forms = []
        for s in range(m):
            hx = nxt(); fc = int(nxt()); forms.append(int(hx, 16))
        bad = [int(nxt()) for _ in range(nb)]
        kt = vs[lv + 1] - vs[lv]
        cols = []
        for j in range(kt):
            col = 0
            for s in range(m):
                if (forms[s] >> (vs[lv] + j)) & 1: col |= 1 << s
            cols.append(col)
        r = rank_gf2(cols)
        per[lv].append((wt, m, nb, r, kt))
    for t in range(NLEV):
        L = per[t]
        if not L: continue
        kt = L[0][4]
        bywt = Counter(w for w, *_ in L)
        s = f"L{t} kt={kt} ncons={len(L)} wt:" + ",".join(f"{w}:{n}" for w, n in sorted(bywt.items()))
        for w in sorted(bywt):
            sub = [x for x in L if x[0] == w]
            ms = Counter(x[1] for x in sub); rs = Counter(x[3] for x in sub)
            fr = sum(x[2] / 2 ** x[1] for x in sub) / len(sub)
            s += f" | w{w} m{dict(sorted(ms.items()))} rank{dict(sorted(rs.items()))} badfrac{fr:.4f}"
        print(s)
main(sys.argv[1])
