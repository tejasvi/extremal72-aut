"""Method usage of lwe per constraint (replicates lwe.c's choice: rank of the level part, kdim, cost)."""
import sys, collections
def rank_cols(cols, m):
    rows = []
    for s in range(m):
        r = 0
        for j, c in enumerate(cols):
            if (c >> s) & 1: r |= 1 << j
        rows.append(r)
    basis = []
    for r in rows:
        for b in basis: r = min(r, r ^ b)
        if r: basis.append(r); basis.sort(reverse=True)
    return len(basis)
fn = sys.argv[1]
lines = open(fn).read().split('\n')
N, NL, NC = map(int, lines[0].split()); vs = list(map(int, lines[1].split()))
pos = 2; cnt = collections.Counter(); per = collections.defaultdict(collections.Counter); perw = collections.Counter()
for c in range(NC):
    lv, wt, m, nb = map(int, lines[pos].split()); pos += 1
    forms = []
    for s in range(m): hx, cc = lines[pos].split(); pos += 1; forms.append(int(hx, 16))
    pos += 1
    kt = vs[lv + 1] - vs[lv]
    cols = [sum(((f >> (vs[lv] + j)) & 1) << s for s, f in enumerate(forms)) for j in range(kt)]
    r = rank_cols(cols, m); kd = kt - r
    costA = 2 ** kt; costB = nb * (2 ** kd + 4.0)
    meth = 2 if r == 0 else (1 if costB < costA else 0)
    cnt[meth] += 1; per[lv][meth] += 1; perw[(wt, meth)] += 1
print(fn.split('/')[-1], 'methods', dict(cnt), 'per level', {k: dict(v) for k, v in sorted(per.items())})
print('  (weight, method) counts', dict(sorted(perw.items())))
