import sys, numpy as np, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
exec(open(HERE + '/control48v4.py').read().split("st, model = solve(S, timeout=1800)")[0])
from v4sat import applym
basis=S['basis']; E=S['E']; ei=S['ei']; W_=S['W']; part=S['part']; K=12; m=24
def Bfrom(w):
    vec=part
    for t in range(S['nW']):
        if (w>>t)&1: vec^=W_[t]
    return {(i,j):(vec>>ei(i,j))&1 for (i,j) in E}
def build(Bd):
    # dual vectors D_j with <D_j, b_i> = delta_ij
    import itertools
    rows=[[basis[i],1<<i] for i in range(K)]; piv=[]; r=0
    for c in range(m):
        p=next((i for i in range(r,K) if (rows[i][0]>>c)&1),None)
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]
        for i in range(K):
            if i!=r and (rows[i][0]>>c)&1: rows[i][0]^=rows[r][0]; rows[i][1]^=rows[r][1]
        piv.append(c); r+=1
    D=[]
    for j in range(K):
        dv=0
        for i,c in enumerate(piv):
            if (rows[i][1]>>j)&1: dv|=1<<c
        D.append(dv)
    gens=[]
    for k in range(K):
        z=0
        for j in range(K):
            if Bd[(min(k,j),max(k,j))]: z^=D[j]
        y=basis[k]; v=0
        for i in range(m):
            zi=(z>>i)&1; yi=(y>>i)&1
            if zi: v|=1<<(2*i)
            if zi^yi: v|=1<<(2*i+1)
        gens.append(v)
    for c in basis:
        v=0
        for i in range(m):
            if (c>>i)&1: v|=3<<(2*i)
        gens.append(v)
    return gens
for line in open('sol48.txt'):
    w=int(line.split('=')[1],16)
    gens=build(Bfrom(w))
    Wc=np.zeros(1,dtype=np.uint64)
    for g in gens: Wc=np.concatenate([Wc,Wc^np.uint64(g)])
    wts=np.bitwise_count(Wc)
    rk=len(np.unique(Wc))
    # beta: pair i -> pair bb[i], positions preserved; alpha: swap within pairs
    beta=[0]*48
    for i in range(24): beta[2*i]=2*bb[i]; beta[2*i+1]=2*bb[i]+1
    alpha=[i^1 for i in range(48)]
    Ws=set(int(x) for x in Wc)
    ok_b=all(applym(beta,g,48) in Ws for g in gens); ok_a=all(applym(alpha,g,48) in Ws for g in gens)
    print(f"solution {w:x}: |C|=2^{int(np.log2(rk))}, min weight {wts[wts>0].min()}, doubly even {bool((wts%4==0).all())}, alpha ok {ok_a}, beta ok {ok_b}")
