import sys
sys.path.insert(0,'.')
from f16 import MUL, CONJ, CLS as PCLS, WT5, NORM
# map python classes to C classes via weight: C uses class 1 = norm 1; 2/3 = the other two norms.
# C's class-2 norm value = norm of smallest a with NRM!=1 ; recompute here identically
w=None
for a in range(1,16):
    if NORM[a]!=1: w=NORM[a]; break
def ccls(a):
    if a==0: return 0
    if NORM[a]==1: return 1
    return 2 if NORM[a]==w else 3
n=0
for line in open(sys.argv[1]):
    u,v,l,pi,hd,sm=map(int,line.split())
    U=[(u>>(4*j))&15 for j in range(7)]; V=[(v>>(4*j))&15 for j in range(7)]
    assert pi==sum(ccls(U[j])*4**j for j in range(7))
    h=0
    for j in range(7): h^=MUL[U[j]][CONJ[V[j]]]
    assert hd==h
    assert sm==sum(MUL[l][U[j]]<<(4*j) for j in range(7))
    n+=1
print("pidx/hdot/smul cross-check OK on",n,"random cases")
