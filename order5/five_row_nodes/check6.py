#!/usr/bin/env python3
"""Independent last-level certificate check (fresh code, numpy).
Input: lines 'DEPTH5: r0 r1 r2 r3 r4' (hex, 7 nibbles; nibble j = coordinate j of the B side),
rows for A-coordinates 0,1,3,2,4 (in that order). For each node:
 (1) validate: rows orthonormal (Hermitian, conj y->y^4) and M(a)+M(aU) >= 16 for all nonzero a
     supported on {0,1,3,2,4};
 (2) enumerate EVERY vector v of F16^7 orthogonal to the 5 rows with <v,v>=1 (the whole complement),
     and test v as the row for A-coordinate 5 against ALL nonzero a supported on {0,1,3,2,4,5} with a_5 != 0.
Report the number of valid sixth rows (expected 0)."""
import sys, itertools
import numpy as np
# ---- GF(16) = GF(2)[x]/(x^4+x^3+x^2+x+1), from scratch
def mul(a,b):
    r=0
    for i in range(4):
        if b>>i & 1: r ^= a<<i
    for d in (7,6,5,4):
        if r>>d & 1: r ^= 0b11111 << (d-4)
    return r
MUL=np.array([[mul(a,b) for b in range(16)] for a in range(16)],dtype=np.uint8)
def pw(a,e):
    r=1
    for _ in range(e): r=mul(r,a)
    return r
CONJ=np.array([pw(a,4) for a in range(16)],dtype=np.uint8)
NORM=[pw(a,5) for a in range(16)]
W=np.array([0 if a==0 else (4 if NORM[a]==1 else 2) for a in range(16)],dtype=np.int64)
assert sorted(W.tolist()).count(4)==5 and sorted(W.tolist()).count(2)==10
# ---- side function M on weight patterns (e8 = lines+p, complements, all, empty)
LINES=[(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
SX=[(frozenset(),0)]+[(frozenset(L),1) for L in LINES]+[(frozenset(range(7))-frozenset(L),0) for L in LINES]+[(frozenset(range(7)),1)]
def M_of_w(w):
    return min(5*len(S)+x+sum(w[i] for i in range(7) if i not in S)-sum(w[i] for i in S) for S,x in SX)
# table over weight codes 0/1/2 (w=0/4/2) base 3
MT=np.zeros(3**7,dtype=np.int64)
for idx in range(3**7):
    t=idx; w=[]
    for j in range(7):
        c=t%3; t//=3; w.append((0,4,2)[c])
    MT[idx]=M_of_w(w)
WCODE=np.array([0 if a==0 else (1 if NORM[a]==1 else 2) for a in range(16)],dtype=np.int64)
POW3=np.array([3**j for j in range(7)],dtype=np.int64)
def Mvec(V):  # V: (N,7) uint8 array of F16 entries -> M values
    return MT[(WCODE[V]*POW3).sum(axis=1)]
def hdot(u,v):
    r=0
    for a,b in zip(u,v): r ^= int(MUL[a][CONJ[b]])
    return r
INV=[0]*16
for a in range(1,16):
    for b in range(1,16):
        if mul(a,b)==1: INV[a]=b
def kernel(Mx):
    """basis of {v : Mx v^T = 0} over GF(16), fresh Gaussian elimination"""
    Mx=[r[:] for r in Mx]; n=7; piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,len(Mx)) if Mx[i][c]),None)
        if p is None: continue
        Mx[r],Mx[p]=Mx[p],Mx[r]
        iv=INV[Mx[r][c]]; Mx[r]=[mul(iv,x) for x in Mx[r]]
        for i in range(len(Mx)):
            if i!=r and Mx[i][c]:
                f=Mx[i][c]; Mx[i]=[x^mul(f,y) for x,y in zip(Mx[i],Mx[r])]
        piv.append(c); r+=1
    free=[c for c in range(n) if c not in piv]
    basis=[]
    for fc in free:
        v=[0]*n; v[fc]=1
        for i,c in enumerate(piv): v[c]=Mx[i][fc]
        basis.append(v)
    return basis
def parse(h):
    x=int(h,16); return [(x>>(4*j))&15 for j in range(7)]
ACOORD=[0,1,3,2,4,5]
import os
T=int(os.environ.get('THRESH','16'))
def combos(rows):
    """all coefficient vectors over len(rows) rows: returns (coefs (N,k), B (N,7))"""
    k=len(rows)
    coefs=np.array(list(itertools.product(range(16),repeat=k)),dtype=np.uint8)
    B=np.zeros((len(coefs),7),dtype=np.uint8)
    R=np.array(rows,dtype=np.uint8)
    for i in range(k):
        B ^= MUL[coefs[:,i][:,None], R[i][None,:]]
    return coefs,B
def Aside(coefs, acoords):
    A=np.zeros((len(coefs),7),dtype=np.uint8)
    for i,c in enumerate(acoords): A[:,c]=coefs[:,i]
    return A
def check_node(rows):
    # (1) orthonormality
    for i in range(5):
        for j in range(5):
            if hdot(rows[i],rows[j]) != (1 if i==j else 0): return ('INVALID-orth',None)
    coefs,B=combos(rows)
    A=Aside(coefs,ACOORD[:5])
    nz=coefs.any(axis=1)
    if not ((Mvec(A)+Mvec(B))[nz] >= T).all(): return ('INVALID-star',None)
    # (2) whole complement: kernel of the 5x7 system sum_j v_j conj(u_ij) = 0, then <v,v> = 1
    K=kernel([[int(CONJ[x]) for x in u] for u in rows])
    assert len(K)==2, 'complement should be 2-dimensional'
    cands=[]
    for c0 in range(16):
        for c1 in range(16):
            v=[int(MUL[c0][K[0][j]])^int(MUL[c1][K[1][j]]) for j in range(7)]
            if any(v) and hdot(v,v)==1:
                assert all(hdot(v,u)==0 for u in rows)
                cands.append(v)
    # chunks of combos ordered by number of nonzero coefficients (only an ordering for speed;
    # every combo is tested before a candidate is accepted)
    nzc=(coefs!=0).sum(axis=1)
    chunks=[np.nonzero(nzc==k)[0] for k in range(6)]
    good=0
    for v in cands:
        vv=np.array(v,dtype=np.uint8); ok=True
        for ch in chunks:
            Bc=B[ch]; Ac=A[ch]
            for lam in range(1,16):
                B6=Bc ^ MUL[lam][vv][None,:]
                A6=Ac.copy(); A6[:,ACOORD[5]]=lam
                if not ((Mvec(A6)+Mvec(B6))>=T).all(): ok=False; break
            if not ok: break
        if ok: good+=1
    return ('OK',(len(cands),good))
def random_orthonormal(k, rng):
    rows=[]
    while len(rows)<k:
        if rows:
            K=kernel([[int(CONJ[x]) for x in u] for u in rows])
        else:
            K=[[1 if j==i else 0 for j in range(7)] for i in range(7)]
        coef=[rng.randrange(16) for _ in K]
        v=[0]*7
        for c,b in zip(coef,K):
            v=[x^mul(c,y) for x,y in zip(v,b)]
        if hdot(v,v)==1: rows.append(v)
    return rows
if __name__=='__main__' and os.environ.get('CONTROL'):
    import random
    rng=random.Random(5)
    done=0
    while done<3:
        rows=random_orthonormal(5,rng)
        st,res=check_node(rows)
        print('control node:',st,res,flush=True)
        if st=='OK': done+=1
    sys.exit(0)
if __name__=='__main__':
    nodes=[]
    for f in sys.argv[1:]:
        for line in open(f):
            if line.startswith('DEPTH5:'):
                nodes.append([parse(h) for h in line.split()[1:6]])
    print(len(nodes),'five-row nodes', flush=True)
    tot_c=0; tot_g=0; bad=0
    for k,rows in enumerate(nodes):
        st,res=check_node(rows)
        if st!='OK': bad+=1; print('node',k,st,flush=True); continue
        tot_c+=res[0]; tot_g+=res[1]
        print('node',k,'valid; complement candidates',res[0],'valid sixth rows',res[1],flush=True)
    print('SUMMARY: nodes',len(nodes),'invalid',bad,'candidates',tot_c,'valid sixth rows',tot_g)
