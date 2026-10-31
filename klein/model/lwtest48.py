"""QR48 control for the level-wise engine: complete search; verify solutions as genuine codes."""
import sys, subprocess, numpy as np, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
exec(open(HERE + '/control48v4.py').read().split("S = setup(Ygens, bb")[0])
from lwprep import build, export, coords_solver
from v4sat import applym, pc
m=24; K=12
L=build(Ygens, bb, m=24, d=12)
export(L,HERE + '/lw_qr48.txt')
out=subprocess.run(['./lwe',HERE + '/lw_qr48.txt'],capture_output=True,text=True).stdout
sols=[int(l.split()[1],16) for l in out.split('\n') if l.startswith('SOLUTION')]
print(out.strip().split('\n')[-1-K] if False else [l for l in out.split('\n') if l.startswith('DONE')][0])
print("solutions:",len(sols))
w=L['w']; E=L['E']; entf=L['entf']
def gram(a):
    G=[[0]*K for _ in range(K)]
    for e,(i,j) in enumerate(E):
        vm,c=entf[e]; v=(pc(vm & a)&1)^c
        G[i][j]=G[j][i]=v
    return G
# dual basis of w: D_j with <D_j, w_i> = delta
rows=[[w[i],1<<i] for i in range(K)]; piv=[]; r=0
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
beta=[0]*48
for i in range(24): beta[2*i]=2*bb[i]; beta[2*i+1]=2*bb[i]+1
alpha=[i^1 for i in range(48)]
ok=0
for a in sols[:6]:
    G=gram(a); gens=[]
    for k in range(K):
        z=0
        for j in range(K):
            if G[k][j]: z^=D[j]
        y=w[k]; v=0
        for i in range(m):
            zi=(z>>i)&1; yi=(y>>i)&1
            if zi: v|=1<<(2*i)
            if zi^yi: v|=1<<(2*i+1)
        gens.append(v)
    for c in w:
        v=0
        for i in range(m):
            if (c>>i)&1: v|=3<<(2*i)
        gens.append(v)
    Wc=np.zeros(1,dtype=np.uint64)
    for g in gens: Wc=np.concatenate([Wc,Wc^np.uint64(g)])
    wts=np.bitwise_count(Wc); Ws=set(int(x) for x in Wc)
    good=(len(Ws)==1<<24 and wts[wts>0].min()==12 and (wts%4==0).all() and all(applym(beta,g,48) in Ws for g in gens) and all(applym(alpha,g,48) in Ws for g in gens))
    ok+=good
print("verified genuine [48,24,12] V4-codes among first 6 solutions:",ok)
