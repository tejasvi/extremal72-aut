# Verify: (1) mass formula => exactly two Type II [16,8] codes up to equivalence (e8+e8, d16+);
# (2) placement of the 2 fixed points: the C0 weight conditions hold iff the fixed points lie in different e8 components;
# (3) the weight conditions for C0 with (14 cycle coords, 2 fixed coords): 5|a|+|x| >= 16 and = 0 mod 4.
import itertools
from math import factorial, prod
N_typeII_16 = prod(2**i+1 for i in range(0,7))
aut_e8e8 = 1344**2*2
aut_d16p = 2**7*factorial(8)
print("number of Type II codes of length 16:", N_typeII_16)
print("16!/|Aut(e8+e8)| + 16!/|Aut(d16+)| =", factorial(16)//aut_e8e8 + factorial(16)//aut_d16p)
assert N_typeII_16 == factorial(16)//aut_e8e8 + factorial(16)//aut_d16p
def span(gens):
    S={0}
    for g in gens:
        S|={s^g for s in S}
    return S
# e8: extended Hamming on 8 points: coordinates 0..6 Fano points + 7 = extension
LINES=[(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
def mask(it): 
    m=0
    for i in it: m|=1<<i
    return m
e8_words = span([mask(L)|(1<<7) for L in LINES])
assert len(e8_words)==16 and sorted(bin(w).count('1') for w in e8_words)==[0]+[4]*14+[8]
e8e8 = {a | (b<<8) for a in e8_words for b in e8_words}
# d16+: d16 = <1111 0..0, 0011 11 0.., ...> duads {0,1},{2,3},...; glue
duads=[(2*i,2*i+1) for i in range(8)]
d16 = span([mask(duads[i]+duads[i+1]) for i in range(7)])
glue = mask([2*i for i in range(8)])  # one point from each duad: weight 8
d16p = d16 | {g^glue for g in d16}
assert len(d16p)==256
for C in (e8e8,d16p):
    for u in C:
        assert bin(u).count('1')%4==0
        for v in C: assert bin(u&v).count('1')%2==0
print("e8+e8 and d16+ are Type II [16,8]: OK")
def ok_placement(C, p, q):
    # fixed points p,q; others are cycle coordinates
    for w in C:
        if w==0: continue
        x = ((w>>p)&1) + ((w>>q)&1)
        a = bin(w).count('1') - x
        if 5*a + x < 16 or (5*a+x)%4: return False
    return True
for name,C in (("e8+e8",e8e8),("d16+",d16p)):
    good=[(p,q) for p,q in itertools.combinations(range(16),2) if ok_placement(C,p,q)]
    same=[(p,q) for p,q in good if (p<8)==(q<8)]
    print(f"{name}: valid fixed-point pairs {len(good)} of 120; same-component pairs among them: {len(same)}")
