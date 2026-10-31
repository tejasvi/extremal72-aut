"""For each word: is any good class achievable at all (ignoring other words)? Independent of the solver."""
import sys
def pc(x): return bin(x).count('1')
def parse(fn):
    L=open(fn).read().split('\n'); nW,nw=map(int,L[0].split()); p=1; words=[]
    for _ in range(nw):
        wt,d,ng=map(int,L[p].split()); p+=1; forms=[]
        for t in range(d):
            m,c=L[p].split(); p+=1; forms.append((int(m,16),int(c)))
        good=set(map(int,L[p].split())) if ng else set(); p+=1; words.append((wt,d,forms,good))
    return nW,words
for fn in sys.argv[1:]:
    nW,words=parse(fn); dead=[]; units=0
    for q,(wt,d,forms,good) in enumerate(words):
        # relations: combinations of forms with zero mask
        basis=[]; rel=[]
        for t,(m,c) in enumerate(forms):
            v,comb,par=m,1<<t,c
            for (bv,bc,bp) in basis:
                if v & (bv & -bv): v^=bv; comb^=bc; par^=bp
            if v: basis.append((v,comb,par))
            else: rel.append((comb,par))
        ach=[g for g in good if all((pc(g&comb)&1)==par for comb,par in rel)]
        if not ach: dead.append((q,wt,d,len(rel)))
        if len(ach)==1: units+=1
    print(fn.split('/')[-1], 'NW',nW,'words',len(words),'words with no achievable good class:',len(dead), dead[:5], 'unit words:',units)
