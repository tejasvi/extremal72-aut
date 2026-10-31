# Explicit 72-bit check: the symmetries used by the search map C(U) to C(U') via a coordinate
# permutation commuting with (a power of) g and fixing C0; plus Lemma 2 with the full min over C0.
import random, itertools, os
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'indep_patterns.py')).read().split("pats=list")[0])
rng=random.Random(20261018)
LS=set(frozenset(L) for L in LINES)
GL=[t for t in itertools.permutations(range(7)) if all(frozenset(t[i] for i in L) in LS for L in LINES)]
assert len(GL)==168
def conj(a): return pw(a,4)
def hd(u,v):
    s=0
    for a,b in zip(u,v): s^=mul(a,conj(b))
    return s
def psi(a):  # 5-bit int, bit k = coefficient of t^k in p(t)*(t+t^2+t^3+t^4) mod t^5-1
    v=0
    for k in range(4):
        if (a>>k)&1:
            for j in range(1,5): v^=1<<((k+j)%5)
    return v
xi=2; MU5=[pw(xi,k) for k in range(5)]
assert sorted(MU5)==sorted(a for a in range(1,16) if cls[a]==0)
def inv(a):
    for b in range(1,16):
        if mul(a,b)==1: return b
def complement(U):
    # basis of {v : sum_j v_j conj(u_j) = 0 for all rows u in U}
    A=[[conj(x) for x in u] for u in U]
    piv=[]; r=0
    for c in range(7):
        p=next((i for i in range(r,len(A)) if A[i][c]),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]
        iv=inv(A[r][c]); A[r]=[mul(iv,x) for x in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[x^mul(f,y) for x,y in zip(A[i],A[r])]
        piv.append(c); r+=1
    basis=[]
    for fc in range(7):
        if fc in piv: continue
        v=[0]*7; v[fc]=1
        for t,pc in enumerate(piv): v[pc]=A[t][fc]
        basis.append(v)
    return basis
def rand_unitary():
    U=[]
    while len(U)<7:
        B=complement(U)
        while True:
            v=[0]*7
            for b in B:
                l=rng.randrange(16)
                v=[x^mul(l,y) for x,y in zip(v,b)]
            if hd(v,v)==1: break
        assert all(hd(v,w)==0 for w in U)
        U.append(v)
    return U
E8=sorted(words, key=lambda w:(len(w[0]),sorted(w[0]),w[1]))
def phi0(SA,xA,SB,xB):
    r=0
    for i in SA: r|=0b11111<<(5*i)
    for j in SB: r|=0b11111<<(35+5*j)
    return r | (xA<<70) | (xB<<71)
def phi1(cA,cB):
    r=0
    for i,a in enumerate(cA): r|=psi(a)<<(5*i)
    for j,b in enumerate(cB): r|=psi(b)<<(35+5*j)
    return r
def vecmat(a,U):
    out=[0]*7
    for i in range(7):
        if a[i]:
            for j in range(7): out[j]^=mul(a[i],U[i][j])
    return out
def code(U):
    gens=[]
    for i in range(7):
        for s in (1,2,4,8):
            a=[0]*7; a[i]=s
            gens.append(phi1(a,vecmat(a,U)))
    for SA,xA in E8:
        for SB,xB in E8:
            gens.append(phi0(SA,xA,SB,xB))
    return rref(gens)
def rref(vs):
    piv={}
    for v in vs:
        while v:
            h=v.bit_length()-1
            if h in piv: v^=piv[h]
            else: piv[h]=v; break
    # full reduction
    keys=sorted(piv)
    for h in keys:
        for h2 in keys:
            if h2!=h and (piv[h2]>>h)&1: piv[h2]^=piv[h]
    return tuple(sorted(piv.values()))
def perm_vec(v,P):   # P: list of 72 targets, bit p -> bit P[p]
    r=0
    for p in range(72):
        if (v>>p)&1: r|=1<<P[p]
    return r
def perm_code(C,P): return rref([perm_vec(v,P) for v in C])
def popc(v): return bin(v).count('1')
gperm=[ (5*(p//5)+(p%5+1)%5) if p<70 else p for p in range(72)]
nt=0
for trial in range(4):
    U=rand_unitary(); C=code(U)
    assert len(C)==36
    assert all(popc(v)%4==0 for v in C) and all(popc(u&v)%2==0 for u in C for v in C)
    assert perm_code(C,gperm)==C
    # (a) mu5 scalings
    kA=[rng.randrange(5) for _ in range(7)]; kB=[rng.randrange(5) for _ in range(7)]
    U2=[[mul(mul(pw(xi,(5-kA[i])%5),U[i][j]),pw(xi,kB[j])) for j in range(7)] for i in range(7)]
    P=list(range(72))
    for i in range(7):
        for k in range(5): P[5*i+k]=5*i+(k+kA[i])%5
    for j in range(7):
        for k in range(5): P[35+5*j+k]=35+5*j+(k+kB[j])%5
    assert code(U2)==perm_code(C,P); nt+=1
    # (b) GL(3,2) on A (rows) and on B (columns), independently
    sA=rng.choice(GL); sB=rng.choice(GL)
    U3=[[0]*7 for _ in range(7)]
    for i in range(7):
        for j in range(7): U3[sA[i]][sB[j]]=U[i][j]
    P=list(range(72))
    for i in range(7):
        for k in range(5): P[5*i+k]=5*sA[i]+k
    for j in range(7):
        for k in range(5): P[35+5*j+k]=35+5*sB[j]+k
    assert code(U3)==perm_code(C,P); nt+=1
    # (c) Frobenius y -> y^2 entrywise = position k -> 2k in every cycle
    U4=[[mul(U[i][j],U[i][j]) for j in range(7)] for i in range(7)]
    P=[(5*(p//5)+(2*(p%5))%5) if p<70 else p for p in range(72)]
    C4=code(U4)
    assert C4==perm_code(C,P); nt+=1
    assert perm_code(C4,gperm)==C4
    # (d) a non-collineation permutation of A must NOT be a symmetry in general (sanity: test has teeth)
    bad=[1,0,2,3,4,5,6]
    if tuple(bad) not in set(GL):
        U5=[U[bad.index(i)] for i in range(7)]
        P=list(range(72))
        for i in range(7):
            for k in range(5): P[5*i+k]=5*bad[i]+k
        assert code(U5)!=perm_code(C,P)
    # Lemma 2 with the full min over the 256 C0 words, on random and on low-M codewords
    for t in range(120):
        a=[rng.randrange(16) if rng.random()<0.5 else 0 for _ in range(7)]
        if not any(a): continue
        b=vecmat(a,U)
        v1=phi1(a,b)
        true=min(popc(v1^phi0(SA,xA,SB,xB)) for SA,xA in E8 for SB,xB in E8)
        f=M([4 if cls[z]==0 else (2 if z else 0) for z in a])+M([4 if cls[z]==0 else (2 if z else 0) for z in b])
        assert true==f,(a,b,true,f)
print("symmetry checks passed:", nt, "; Lemma 2 (full min over C0) verified on random words")
