# Explicit 72-bit model of C = phi0(C0) + phi1(C1) to verify the reduction.
import random, itertools, sys
sys.path.insert(0,'.')
from f16 import MUL, CONJ, NORM, CLS, PSI, WT5
LINES = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]   # Fano plane on 7 points
# e8 on (7 cycle coords of a side) + fixed point: list of (S, x)
E8 = [((),0)] + [(L,1) for L in LINES] + [(tuple(i for i in range(7) if i not in L),0) for L in LINES] + [(tuple(range(7)),1)]
def hdot(u,v):
    r=0
    for a,b in zip(u,v): r ^= MUL[a][CONJ[b]]
    return r
def rand_isotropic_maximal(n=14, rng=random):
    basis=[]
    while len(basis)<n//2:
        v=[rng.randrange(16) for _ in range(n)]
        if all(x==0 for x in v): continue
        if hdot(v,v)!=0: continue
        if any(hdot(v,b)!=0 for b in basis): continue
        # independence check via span (small dims fine): reduce
        if in_span(v,basis): continue
        basis.append(v)
    return basis
def inv(a):
    for b in range(1,16):
        if MUL[a][b]==1: return b
def in_span(v,basis):
    # Gaussian elimination over F16
    rows=[list(b) for b in basis]
    piv=[]
    M=[r[:] for r in rows]
    # echelon
    r=0; pc=[]
    for c in range(len(v)):
        p=None
        for i in range(r,len(M)):
            if M[i][c]: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        iv=inv(M[r][c]); M[r]=[MUL[iv][x] for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[x^MUL[f][y] for x,y in zip(M[i],M[r])]
        pc.append(c); r+=1
    w=v[:]
    for i,c in enumerate(pc):
        if w[c]:
            f=w[c]; w=[x^MUL[f][y] for x,y in zip(w,M[i])]
    return all(x==0 for x in w)
def phi1(c):   # 14 F16 coords -> 72-bit int (cycles i at bits 5i..5i+4, fixed bits 70,71 = 0)
    r=0
    for i,a in enumerate(c): r |= PSI[a] << (5*i)
    return r
def phi0(aA, xA, aB, xB):   # aA,aB: sets of cycle indices within side (0..6); x bits
    r=0
    for i in aA: r |= 0b11111 << (5*i)
    for i in aB: r |= 0b11111 << (5*(7+i))
    if xA: r |= 1<<70
    if xB: r |= 1<<71
    return r
def hval(S,x,w):
    Ss=set(S)
    return 5*len(S)+x+sum(w[i] for i in range(7) if i not in Ss)-sum(w[i] for i in S)
def Mside(w):
    return min(hval(S,x,w) for S,x in E8)
def wpat(c): return [WT5[a] for a in c]
if __name__=="__main__":
    rng=random.Random(1)
    B=rand_isotropic_maximal(14,rng)
    # binary generators
    gens=[]
    for b in B:
        for s in (1,2,4,8):   # F2-basis 1,x,x^2,x^3 of F16
            gens.append(phi1([MUL[s][a] for a in b]))
    for S,x in E8[1:]:
        pass
    # C0 = e8 + e8 generators: all 16x16 words; take a basis via elimination
    c0words=[phi0(SA,xA,SB,xB) for (SA,xA) in E8 for (SB,xB) in E8]
    allg = gens + c0words
    # rank over F2
    def rank(vs):
        basis=[];
        for v in vs:
            for b in basis:
                v=min(v, v^b)
            if v: basis.append(v)
        return len(basis), basis
    rk, basis = rank(allg)
    print("rank", rk)
    assert rk==36
    for u in basis:
        assert bin(u).count('1')%4==0
        for v in basis:
            assert bin(u&v).count('1')%2==0
    print("C is self-dual and doubly even: OK")
    # random codewords: check weight formula
    for t in range(3000):
        coeffs=[rng.randrange(16) for _ in range(7)]
        c=[0]*14
        for k,b in zip(coeffs,B):
            for j in range(14): c[j]^=MUL[k][b[j]]
        (SA,xA)=rng.choice(E8); (SB,xB)=rng.choice(E8)
        v = phi1(c) ^ phi0(SA,xA,SB,xB)
        w=wpat(c)
        assert bin(v).count('1') == hval(SA,xA,w[:7]) + hval(SB,xB,w[7:]), "formula mismatch"
    print("weight formula h_A + h_B verified on 3000 random words")
