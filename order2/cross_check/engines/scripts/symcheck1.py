"""Semantic check of an LTS-1 symmetry file (SYMFILE of lwe3/lwe5): 'm c0 nent' / canon (2^m) / per orbit word
u != w0: 'c_u rows'.  w0 = first flag vector, S0 = Stab_G(w0); canon[s] = min_{h in S0} s o h; rows of u =
coords_u(g_u ub0_j) with g_u the first element of G (builder's indexing) mapping w0 to u.  Audit code.
Usage: symcheck1.py PKGDIR(flag.txt, inst.txt.meta) SYMFILE CI"""
import sys, os, pickle
sys.path.insert(0, '<HOME>/c72/audit/c2audit/engine-check/scripts')
from indep_c2 import load_codes, CODES
from symcheck import closure, ap, coords_in, fail
M = 36
pkg, symf, ci = sys.argv[1], sys.argv[2], int(sys.argv[3])
Y = load_codes(CODES)[ci]; S = [0]
for g in Y: S = S + [s ^ g for s in S]
Yset = set(S)
G = closure([list(g) for g in pickle.load(open('<HOME>/c72/c2par/invs.pkl', 'rb'))[ci]['perms']], M)
if any(ap(g, y) not in Yset for g in G for y in Y): fail('G not in Aut(Y)')
meta = [list(map(int, l.split())) for l in open(os.path.join(pkg, 'inst.txt.meta')) if l.strip()]
idx = {row[0]: k for k, row in enumerate(meta)}
w0 = int(open(os.path.join(pkg, 'flag.txt')).read().split()[1])
tok = list(map(int, open(symf).read().split()))
m, c0, nent = tok[0], tok[1], tok[2]; pos = 3
canon = tok[pos:pos + (1 << m)]; pos += 1 << m
ents = []
for _ in range(nent): ents.append((tok[pos], tok[pos + 1:pos + 1 + m])); pos += 1 + m
if pos != len(tok): fail('trailing')
if c0 != idx[w0] or m != len(meta[c0]) - 1: fail('c0/m')
ub0 = meta[c0][1:]; co0 = coords_in(ub0)
S0 = [g for g in G if ap(g, w0) == w0]
acts = [[co0(ap(h, ub0[j])) for j in range(m)] for h in S0]
def act(rows, s):
    return sum((((rr & s).bit_count() & 1) << j) for j, rr in enumerate(rows))
for s in range(1 << m):
    if canon[s] != min(act(rw, s) for rw in acts): fail(f'canon[{s}]')
O = {}
for g in G:
    u = ap(g, w0)
    if u not in O: O[u] = g
others = [u for u in O if u != w0]
if len(others) != nent: fail('orbit size')
for (cu, rows), u in zip(ents, others):
    if cu != idx[u]: fail('c_u')
    if rows != [coords_in(meta[cu][1:])(ap(O[u], ub0[j])) for j in range(m)]: fail('rows')
print(f'RESULT PASS LTS-1 file: |G| {len(G)} |S0| {len(S0)} orbit {len(O)} m {m} classes {len(set(canon))}')
