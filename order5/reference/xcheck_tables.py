import sys
sys.path.insert(0,'.')
from f16 import MUL, CONJ, NORM, WT5
from model import Mside
L=open(sys.argv[1]).read().split('\n')
cm=[list(map(int,L[i].split())) for i in range(16)]
assert cm==MUL, "MUL differs"
for a in range(16):
    c,n,cl,w=map(int,L[16+a].split())
    assert c==CONJ[a] and n==NORM[a] and w==WT5[a], a
M=[int(L[32+i]) for i in range(1<<14)]
for idx in range(1<<14):
    t=idx; w=[]
    for j in range(7):
        c=t&3; t>>=2; w.append(0 if c==0 else (4 if c==1 else 2))
    assert M[idx]==Mside(w), (idx,w,M[idx],Mside(w))
print("C tables == Python reference: OK")
