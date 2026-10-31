# Independent pattern-level checks (own field arithmetic, own e8, own GL(3,2)).
import itertools
from collections import Counter, defaultdict
# F16 = F2[x]/(x^4+x^3+x^2+x+1)
def mul(a,b):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a&16: a^=0b11111
    return r
def pw(a,e):
    r=1
    for _ in range(e): r=mul(r,a)
    return r
F=list(range(16))
norm={a:pw(a,5) for a in F}
F4=sorted(set(norm.values())); assert len(F4)==4
# F4* is cyclic of order 3; pick generator om (any element of F4 other than 0,1)
om=[z for z in F4 if z not in (0,1)][0]
F4exp={1:0, om:1, mul(om,om):2}
assert len(F4exp)==3
# exponent class of a nonzero element = discrete log of its norm in F4* (0 means norm 1)
cls={a:(None if a==0 else F4exp[norm[a]]) for a in F}
assert sum(1 for a in F if cls[a]==0)==5
# psi weights: binary weight of p(t)*(t+t^2+t^3+t^4) mod t^5-1
def psiw(a):
    v=[0]*5
    for k in range(4):
        if (a>>k)&1:
            for j in range(1,5): v[(k+j)%5]^=1
    return sum(v)
for a in F[1:]:
    assert psiw(a)==(4 if cls[a]==0 else 2)
LINES=[(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
# e8 = span of (L u {inf}); words as (frozenset S, x)
gens=[(frozenset(L),1) for L in LINES]
words={(frozenset(),0)}
for g in gens:
    words|={(S^g[0], x^g[1]) for (S,x) in words}
assert len(words)==16
assert sorted(len(S)+x for S,x in words)==[0]+[4]*14+[8]
def M(wts):  # wts: list of 7 binary weights
    W=sum(wts)
    return min(5*len(S)+x+W-2*sum(wts[i] for i in S) for S,x in words)
# patterns: tuple of 7 entries in {None,0,1,2} (None = zero coordinate, k = class exponent)
def wt(e): return 0 if e is None else (4 if e==0 else 2)
def shift(p,k): return tuple(None if e is None else (e+k)%3 for e in p)
def nsum(p):  # sum of norms in F4
    s=0
    for e in p:
        if e is not None: s^=[1,om,mul(om,om)][e]
    return s
pats=list(itertools.product([None,0,1,2],repeat=7))
Mp={p:M([wt(e) for e in p]) for p in pats}
# GL(3,2): permutations preserving the line set
LS=set(frozenset(L) for L in LINES)
GL=[s for s in itertools.permutations(range(7)) if all(frozenset(s[i] for i in L) in LS for L in LINES)]
print("GL(3,2) order:", len(GL))
def img(p,s,sw):
    q=[None]*7
    for j in range(7):
        e=p[j]
        if e is not None and sw: e=(-e)%3
        q[s[j]]=e
    return tuple(q)
def nz(p): return sum(e is not None for e in p)
T=16
R=[p for p in pats if nsum(p)==1 and all(Mp[shift(p,k)]+(4 if k==0 else 2)>=T for k in range(3))]
print("|R| =", sum(5**nz(p) for p in R), " patterns:", len(R))
# orbits under GL x swap
orb={}
for p in R:
    if p in orb: continue
    O={img(p,s,sw) for s in GL for sw in (0,1)}
    for q in O: orb[q]=min(O, key=lambda t: tuple(-1 if e is None else e for e in t))
cnt=Counter()
for p in R: cnt[orb[p]]+=5**nz(p)
print("orbits:", len(cnt))
for k,v in sorted(cnt.items(), key=lambda kv: kv[1]):
    print("  orbit rep", k, "rows", v, "weight pattern", sorted(wt(e) for e in k))
# Lemma 3: nonzero isotropic with M(lambda v)>=16 for all lambda
bad=[p for p in pats if nz(p)>0 and nsum(p)==0 and all(Mp[shift(p,k)]>=16 for k in range(3))]
print("Lemma 3 counterexample patterns:", len(bad))
# M histogram, and check M always even, M(v)>=2 for v!=0
assert all(m%2==0 for m in Mp.values())
assert all(Mp[p]>=2 for p in pats if nz(p)>0)
print("M even and >=2 on nonzero: OK; max M =", max(Mp.values()))
