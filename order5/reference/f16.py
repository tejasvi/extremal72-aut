# Reference implementation (slow, for verification) of the C5 reduction.
# F16 = F2[x]/(Phi5), Phi5 = x^4+x^3+x^2+x+1; elements = ints 0..15 (bit k = coeff of x^k).
import itertools, random
PHI5 = 0b11111
def gmul(a,b):
    r=0
    for i in range(4):
        if (b>>i)&1: r ^= a<<i
    for d in range(7,3,-1):
        if (r>>d)&1: r ^= PHI5<<(d-4)
    return r
MUL=[[gmul(a,b) for b in range(16)] for a in range(16)]
def gpow(a,e):
    r=1
    for _ in range(e): r=MUL[r][a]
    return r
CONJ=[gpow(a,4) for a in range(16)]          # x -> x^4 (Frobenius^2), fixed field F4
NORM=[gpow(a,5) for a in range(16)]          # norm to F4
F4 = sorted(set(NORM))                         # {0,1,w,w^2}
assert len(F4)==4
# class: 0 for zero, 1 for norm 1 (5th roots of unity), 2/3 for the two other norm classes
w_elem = [n for n in F4 if n not in (0,1)][0]
CLS=[0]*16
for a in range(1,16):
    n=NORM[a]; CLS[a]= 1 if n==1 else (2 if n==w_elem else 3)
# psi: F16 -> even-weight 5-bit vectors, p(x) |-> p(t)*e1 in F2[t]/(t^5-1), e1 = t+t^2+t^3+t^4
def rmul5(u,v):  # 5-bit cyclic polynomial product
    r=0
    for i in range(5):
        if (u>>i)&1:
            for j in range(5):
                if (v>>j)&1: r ^= 1<<((i+j)%5)
    return r
E1 = 0b11110
def psi(a):
    p=0
    for k in range(4):
        if (a>>k)&1: p ^= 1<<k
    return rmul5(p,E1)
PSI=[psi(a) for a in range(16)]
WT5=[bin(PSI[a]).count('1') for a in range(16)]
for a in range(16):
    assert WT5[a] == (0 if a==0 else (4 if CLS[a]==1 else 2)), (a,WT5[a],CLS[a])
assert len(set(PSI))==16
# psi is a ring iso onto the even-weight code
for a in range(16):
    for b in range(16):
        assert PSI[MUL[a][b]] == rmul5(PSI[a],PSI[b])
        assert PSI[a^b] == PSI[a]^PSI[b]
print("F16 / psi checks OK; elements per class:", [CLS.count(c) for c in range(4)])
