import sys, math
sys.path.insert(0, "<HOME>/c72_indep/src")
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[0])
exec(open("<HOME>/c72_indep/src/explore3.py").read().split("# ---- greedy simulation ----")[1].split("R = Basis()")[0])
O16 = [0, 1, 2, 6, 15, 17, 18, 23, 27, 29, 30, 31, 32, 33, 34, 35]
O2 = [3, 28]
O18 = [4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 19, 20, 21, 22, 24, 25, 26]
m16 = sum(1 << i for i in O16); m2 = sum(1 << i for i in O2); m18 = sum(1 << i for i in O18)
U = [v for v in words if v & ~(m18 | m2) == 0]
Ub = rref(U, n)
lowset = set(low)
# cosets of U
seen = set()
res = []
for y in words:
    if y in seen: continue
    cos = [y ^ u for u in U]
    for c in cos: seen.add(c)
    lw = [c for c in cos if c in lowset]
    pw = -sum(logfrac[c] for c in lw)
    cnt = Counter(wt(c) for c in lw)
    res.append((pw, cnt[8], cnt[10], cnt[12], min(cos, key=wt)))
res.sort(reverse=True)
print("number of cosets", len(res))
for r in res[:15]:
    print("power %.2f w8=%d w10=%d w12=%d minwt rep %d" % (r[0], r[1], r[2], r[3], wt(r[4])))
