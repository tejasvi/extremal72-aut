import sys, itertools, os
sys.argv=[sys.argv[0]]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'indep_patterns.py')).read().split("pats=list")[0])
L=open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'search', 'tables_c.txt')).read().split('\n')
C_M=[int(L[32+i]) for i in range(1<<14)]
# C field tables
CM=[list(map(int,L[i].split())) for i in range(16)]
assert all(CM[a][b]==mul(a,b) for a in range(16) for b in range(16)), "MUL differs from independent field"
bad=0
for idx in range(1<<14):
    w=[]
    t=idx
    for j in range(7):
        c=t&3; t>>=2; w.append(0 if c==0 else (4 if c==1 else 2))
    if C_M[idx]!=M(w): bad+=1
print("Mtab mismatches vs independent M:", bad)
# class/weight table check
for a in range(16):
    c,n,cl,wv=map(int,L[16+a].split())
    assert n==norm[a] and c==pw(a,4) and wv==psiw(a)
    assert (cl==0)==(a==0) and ((cl==1)==(a!=0 and cls[a]==0))
print("CONJ/NRM/WT5 tables agree with independent field")
