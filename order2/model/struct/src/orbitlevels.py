"""For an instance + Aut(Y) generators: G-orbits of the low words (constraints) and, per orbit, the max level of its
words (the level at which a lex-leader comparison over the whole orbit becomes decidable).  Prints the orbits whose
max level is smallest (candidate key words whose orbit is complete early)."""
import sys, pickle
sys.path.insert(0, '<HOME>/c72/c2opt/struct/src')
from instio import read_inst
ci = int(sys.argv[1]); I = read_inst(sys.argv[2]); cons = I['cons']
perms = pickle.load(open('<HOME>/c72/c2opt/struct/inst/invs.pkl', 'rb'))[ci]['perms']
def ap(p, y):
    z = 0
    while y:
        b = y & -y; i = b.bit_length() - 1; z |= 1 << p[i]; y ^= b
    return z
lev = {c['y']: c['lv'] for c in cons}; wt = {c['y']: c['wt'] for c in cons}
seen = set(); orbs = []
for c in cons:
    y = c['y']
    if y in seen: continue
    orb = {y}; st = [y]
    while st:
        x = st.pop()
        for p in perms:
            z = ap(p, x)
            if z not in orb: orb.add(z); st.append(z)
    seen |= orb
    orbs.append((max(lev[x] for x in orb), len(orb), wt[y], sorted(lev[x] for x in orb)))
orbs.sort()
print("orbits:", len(orbs))
for o in orbs[:15]: print(f"maxlev {o[0]:2d} size {o[1]:4d} wt {o[2]:2d} levels {o[3][:24]}{'...' if len(o[3])>24 else ''}")
