import sys, math
sys.path.insert(0, "<HOME>/c72_indep/src")
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[0])
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[1].split("R = Basis()")[0])
O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
m16 = sum(1 << i for i in O16); m2 = sum(1 << i for i in O2); m18 = sum(1 << i for i in O18)
def report(name, P):
    R = Basis()
    for f in diag: R.add(f)
    base = len(R.B)
    for y in P:
        for f in funcs[y]: R.add(f)
    cov = [z for z in low if R.rank_mod(funcs[z]) == 0]
    cnt = Counter(wt(z) for z in cov)
    lg = len(R.B) - base + sum(logfrac[z] for z in cov)
    print(f"{name}: |P|={len(P)} dim={len(R.B)-base} covered w8={cnt[8]} w10={cnt[10]} w12={cnt[12]} log2est={lg:.2f}", flush=True)
    return R
U8 = [y for y in low if wt(y) == 8 and y & ~(m18 | m2) == 0]
V8 = [y for y in low if wt(y) == 8 and y & ~(m16 | m2) == 0]
U18 = [y for y in low if wt(y) == 8 and y & ~m18 == 0]
V16 = [y for y in low if wt(y) == 8 and y & ~m16 == 0]
report("U8 (O18+O2)", U8)
report("V8 (O16+O2)", V8)
report("U18 (O18)", U18)
report("V16 (O16)", V16)
report("U8+V8", U8 + V8)
