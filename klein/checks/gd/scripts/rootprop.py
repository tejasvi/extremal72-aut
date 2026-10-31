"""Independent unit propagation (own linear algebra): add the unique achievable class of unit words as equations,
re-reduce all words, until conflict or fixpoint."""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE + '/../scripts')
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
    nW,words=parse(fn)
    piv={}   # highest-bit pivot -> (mask, rhs), fully reduced (RREF)
    def reduce(m,c):
        for h in sorted(piv,reverse=True):
            if (m>>h)&1: pm,pr=piv[h]; m^=pm; c^=pr
        return m,c
    def add(m,c):
        m,c=reduce(m,c)
        if m==0: return c==0
        h=m.bit_length()-1
        for k in list(piv):
            pm,pr=piv[k]
            if (pm>>h)&1: piv[k]=(pm^m,pr^c)
        piv[h]=(m,c); return True
    rnd=0; status='fixpoint'
    while True:
        rnd+=1; newunits=0; conflict=None
        for q,(wt,d,forms,good) in enumerate(words):
            red=[reduce(m,c) for (m,c) in forms]
            basis=[]; rel=[]
            for t,(m,c) in enumerate(red):
                v,comb,par=m,1<<t,c
                for (bv,bc,bp) in basis:
                    if v & (bv & -bv): v^=bv; comb^=bc; par^=bp
                if v: basis.append((v,comb,par))
                else: rel.append((comb,par))
            ach=[g for g in good if all((pc(g&comb)&1)==par for comb,par in rel)]
            if not ach: conflict=(q,wt); break
            if len(ach)==1 and basis:
                g=ach[0]
                for t,(m,c) in enumerate(red):
                    if m:
                        if not add(m, ((g>>t)&1)^c): conflict=(q,wt,'eq'); break
                if conflict: break
                newunits+=1
        if conflict: status=f'CONFLICT at word {conflict} in round {rnd}'; break
        if newunits==0: break
    print(fn.split('/')[-1], status, 'equations', len(piv))
