"""Semantic check of an LTSB file (bit-granular LTS data) against its definition (audit, independent code).
usage: ltsbcheck.py CI INST LTSH LTSB [KEYFILE]   (KEYFILE: 'KEY w0 w1 ...'; the LTSB key constraint must hold w0)
Definition: for g in G = Aut(Y) and bit j of the key word's syndrome, the transported bit is
  s_k0(B^g)_j = B(g k0, g ub0_j) = sum_i R_ij * s_{c_u, i}(B),  u = g k0,  R_j = coordinates of g ub0_j in the basis ub(c_u),
an affine form over the instance variables. Every LTSB line must equal (F_j, c_j) for some genuine automorphism g
(generators from explore's frozen invs.pkl, each checked to preserve Y; closure by BFS), with lv = level of c_u and
L_j = level of the highest variable of F_j (-1 for F = 0). A line that matches no automorphism would let the engine
prune with foreign data. Also: header (nG, m0, c0) vs the LTSH header and the instance."""
import sys, pickle
ci, inst, ltsh, ltsb = int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4]
keyf = sys.argv[5] if len(sys.argv) > 5 else None
FROZ = '<HOME>/c72/explore/runs2/frozen/'
probs = []
# ---- code Y and its automorphism group
inv = pickle.load(open(FROZ + 'invs.pkl', 'rb'))[ci]
codes = []
for b in open(FROZ + 'codes36.txt').read().strip().split('\n\n'):
    rows = [l.strip() for l in b.strip().split('\n') if l.strip()]
    codes.append([sum(int(ch) << j for j, ch in enumerate(r)) for r in rows])
Ygen = codes[ci]
def red(basis, v):
    for x in basis: v = min(v, v ^ x)
    return v
Yb = []
for g in Ygen:
    r = red(Yb, g)
    if r: Yb.append(r); Yb.sort(reverse=True)
assert len(Yb) == 18
def ap(p, x):
    o = 0
    for i in range(36):
        if (x >> i) & 1: o |= 1 << p[i]
    return o
gens = [tuple(p) for p in inv['perms']]
for p in gens:
    assert sorted(p) == list(range(36)) and all(red(Yb, ap(p, y)) == 0 for y in Ygen), 'generator not in Aut(Y)'
idp = tuple(range(36)); G = [idp]; seen = {idp}; k = 0
while k < len(G):
    x = G[k]; k += 1
    for s in gens:
        y = tuple(s[x[i]] for i in range(36))
        if y not in seen: seen.add(y); G.append(y)
# ---- instance: N, levels, constraints (forms, consts) and meta (word, basis)
toks = open(inst).read().split(); it = iter(toks)
N, NLEV, NC = int(next(it)), int(next(it)), int(next(it))
vstart = [int(next(it)) for _ in range(NLEV + 1)]
cons = []
for c in range(NC):
    lv, wt, m, nbad = int(next(it)), int(next(it)), int(next(it)), int(next(it))
    fm = []; fc = []
    for _ in range(m): fm.append(int(next(it), 16)); fc.append(int(next(it)))
    for _ in range(nbad): next(it)
    cons.append({'lv': lv, 'm': m, 'fm': fm, 'fc': fc})
meta = [list(map(int, l.split())) for l in open(inst + '.meta').read().strip().split('\n')]
assert len(meta) == NC
for c, row in enumerate(meta):
    cons[c]['y'] = row[0]; cons[c]['ub'] = row[1:]
    assert len(row) - 1 == cons[c]['m'], f'constraint {c}: meta basis size'
idx = {c['y']: k for k, c in enumerate(cons)}
def level_of(F):
    if F == 0: return -1
    b = F.bit_length() - 1
    for t in range(NLEV):
        if vstart[t] <= b < vstart[t + 1]: return t
    raise ValueError('variable index out of range')
def coords(basis, v):
    """coordinates of v in the given basis (list of ints), by Gaussian elimination; None if v is not in the span"""
    rows = [(b, 1 << i) for i, b in enumerate(basis)]   # (vector, coefficient mask)
    piv = []
    for vec, msk in rows:
        for pv, pm in piv:
            if vec ^ pv < vec: vec ^= pv; msk ^= pm
        if vec: piv.append((vec, msk)); piv.sort(reverse=True)
        else: return 'dependent'
    msk = 0
    for pv, pm in piv:
        if v ^ pv < v: v ^= pv; msk ^= pm
    return msk if v == 0 else None
# ---- LTSH and LTSB headers
lh = open(ltsh).readline().split()
assert lh[0] == 'LTSH'
LHm0, LHc0, LHnG = int(lh[2]), int(lh[3]), int(lh[6])
lb = open(ltsb).read().split('\n')
hd = lb[0].split()
if hd[0] != 'LTSB': probs.append('bad LTSB header')
nG, m0, c0 = int(hd[1]), int(hd[2]), int(hd[3])
if (nG, m0, c0) != (LHnG, LHm0, LHc0): probs.append(f'LTSB header {nG, m0, c0} != LTSH {LHnG, LHm0, LHc0}')
if nG != len(G): probs.append(f'LTSB nG {nG} != |Aut(Y)| closure {len(G)}')
k0 = cons[c0]['y']; ub0 = cons[c0]['ub']
if len(ub0) != m0: probs.append('m0 != basis size of the key constraint')
if keyf:
    kw = [int(x) for x in [l for l in open(keyf) if l.startswith('KEY')][0].split()[1:]]
    if not kw or kw[0] != k0: probs.append(f'key constraint {c0} holds word {k0}, but the key file starts with {kw[:1]}')
    # the LTSH key components must be the key file's words, in order (LTSH line 2: c_i m_i pairs)
    l2 = open(ltsh).read().split('\n')[1].split()
    kc = [int(l2[2 * i]) for i in range(len(l2) // 2)]
    if [cons[c]['y'] for c in kc] != kw: probs.append(f'LTSH key words {[cons[c]["y"] for c in kc]} != key file {kw}')
# ---- expected (F_j, c_j) per automorphism
expect = {}
for g in G:
    u = ap(g, k0)
    if u not in idx: probs.append('image of k0 has no constraint'); break
    X = cons[idx[u]]; tup = []
    for j in range(m0):
        R = coords(X['ub'], ap(g, ub0[j]))
        if not isinstance(R, int): probs.append(f'g ub0_{j} not in span of ub(c_u)'); R = 0
        F = 0; c = 0
        for i in range(X['m']):
            if (R >> i) & 1: F ^= X['fm'][i]; c ^= X['fc'][i]
        tup.append((F, c))
    expect.setdefault(tuple(tup), []).append((g, X['lv']))
# ---- compare every LTSB line
lines = [l for l in lb[1:] if l.strip()]
if len(lines) != nG: probs.append(f'{len(lines)} lines, header nG {nG}')
matched = 0; used = {}; badlv = badL = 0; unmatched = []
for n, l in enumerate(lines):
    f = l.split()
    lvu = int(f[0]); tup = []; Ls = []
    for j in range(m0):
        F = int(f[1 + 3 * j], 16); c = int(f[2 + 3 * j]); L = int(f[3 + 3 * j])
        tup.append((F, c)); Ls.append(L)
        if L != level_of(F): badL += 1
    hit = expect.get(tuple(tup))
    if not hit: unmatched.append(n); continue
    matched += 1; used[tuple(tup)] = used.get(tuple(tup), 0) + 1
    if lvu != hit[0][1]: badlv += 1
over = sum(1 for t, cnt in used.items() if cnt > len(expect[t]))
if unmatched: probs.append(f'{len(unmatched)} lines match no automorphism, e.g. lines {unmatched[:5]}')
if badlv: probs.append(f'{badlv} lines with a wrong lv(c_u)')
if badL: probs.append(f'{badL} bit levels differ from the level of their form')
if over: probs.append(f'{over} transported syndromes listed more often than automorphisms give them')
print(f'LTSB {ltsb}: |G| {len(G)}, m0 {m0}, key constraint {c0} (word {k0}, level {cons[c0]["lv"]}); lines {len(lines)}, '
      f'matched {matched}, distinct transported syndromes {len(expect)}')
for p in probs: print('PROBLEM:', p)
print('VERDICT', 'PASS' if not probs else 'FAIL')
