"""QR72 (d=12) planted test for the level-wise engine at length 72: pin the low-level variables to QR72's own
(gauge-normalised) form, leave the top variables free, check that the engine finds QR72's assignment."""
import sys, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE)
src=open(HERE + '/control72v4.py').read().split("S = setup(Ygens, bb")[0]
exec(src)
from lwprep import build, export, coords_solver
from v4sat import applym, pc
m=36; K=18
L=build(Ygens, bb, m=36, d=12)
w=L['w']; E=L['E']; entf=L['entf']; N=L['N']; free=L['free']; level=L['level']
# QR72's Gram matrix in the w-basis: B(w_i,w_j) = <z(w_i), w_j>, z(y) = z-part of a codeword with pair-sum y
imgs=[proj(g) for g in Cb]
redl=[]
for i,(y,z) in enumerate(imgs):
    r=y; c=1<<i
    for (pr,pcc,bit) in redl:
        if (r>>bit)&1: r^=pr; c^=pcc
    if r: redl.append((r,c,r.bit_length()-1))
def pre(y):
    r=y; c=0
    for (pr,pcc,bit) in redl:
        if (r>>bit)&1: r^=pr; c^=pcc
    assert r==0
    v=0
    for i in range(36):
        if (c>>i)&1: v^=Cb[i]
    return v
zw=[proj(pre(w[k]))[1] for k in range(K)]
Gq={(i,j): pc(zw[i]&w[j])&1 for (i,j) in E}
# gauge-normalise: find gauge combination g with (Gq+g)|F = 0 ; F = entries that are gauge pivots -> they are
# exactly the dependent entries fixed to 0.  Easiest: search over the 2^rank gauge combinations is too big; instead
# solve: unknown coefficients a over gauge vectors, equations (Gq + sum a_r Delta_r)(e) = 0 for e in F.
orbs=[];seen=set()
for p in range(36):
    if p in seen: continue
    orbs.append((p,bb[p])); seen|={p,bb[p]}
def Dvec(R): return {(i,j): pc(w[i]&w[j]&R)&1 for (i,j) in E}
gauges=[Dvec((1<<p)|(1<<q)) for (p,q) in orbs]
T=0
for (p,q) in orbs: T|=1<<p
gauges.append(Dvec(T))
# F = gauge pivots chosen by lwprep (lowest-index elimination) -> recompute the same way
eidx={e:n for n,e in enumerate(E)}
gp={}
for gv in gauges:
    g=0
    for e,v in gv.items():
        if v: g|=1<<eidx[e]
    for b in sorted(gp):
        if (g>>b)&1: g^=gp[b]
    if g:
        b=(g&-g).bit_length()-1
        for b2 in list(gp):
            if (gp[b2]>>b)&1: gp[b2]^=g
        gp[b]=g
Gv=0
for e,v in Gq.items():
    if v: Gv|=1<<eidx[e]
for b,g in gp.items():
    if (Gv>>b)&1: Gv^=g
assert all(not (Gv>>b)&1 for b in gp)
# assignment: free entries' values
a=0
for n,e in enumerate(free):
    if (Gv>>e)&1: a|=1<<n
# consistency: every entry form evaluates to Gv
bad=sum(1 for e in range(len(E)) if ((pc(entf[e][0]&a)&1)^entf[e][1])!=((Gv>>e)&1))
print("QR72 normalised form reproduced by the parametrisation:", bad==0)
# pin all variables of levels < PL; append unit constraints
for PL in (int(x) for x in sys.argv[1:]):
    pinned=[v for v in range(N) if level[v]<PL]
    cons=list(L['cons'])
    for v in pinned:
        cons.append((level[v],0,[(1<<v,0)],[1-((a>>v)&1)]))   # syndrome = value; bad = the wrong value
    L2=dict(L); L2['cons']=cons
    export(L2,HERE + '/lw_qr72pin.txt')
    out=subprocess.run(['timeout','1200','./lwe',HERE + '/lw_qr72pin.txt'],capture_output=True,text=True).stdout
    sols=[int(l.split()[1],16) for l in out.split('\n') if l.startswith('SOLUTION')]
    done=[l for l in out.split('\n') if l.startswith('DONE')]
    print(f"pin levels <{PL}: {len(pinned)} pinned, {N-len(pinned)} free: solutions {len(sols)}, QR72 found {a in sols}, {done[0] if done else 'TIMEOUT'}",flush=True)
