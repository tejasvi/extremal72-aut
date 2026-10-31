"""Independent exhaustive search (own code, no shared logic with v4gd*): propagation of unit words over a
fully-reduced linear system, branching on the undetermined word with the fewest achievable good classes.
Prints UNSAT (exhaustive) or the solutions' system. Intended for small trees."""
import sys, time
sys.setrecursionlimit(10000)
def pc(x): return bin(x).count('1')
def parse(fn):
    L=open(fn).read().split('\n'); nW,nw=map(int,L[0].split()); p=1; words=[]
    for _ in range(nw):
        wt,d,ng=map(int,L[p].split()); p+=1; forms=[]
        for t in range(d):
            m,c=L[p].split(); p+=1; forms.append((int(m,16),int(c)))
        good=set(map(int,L[p].split())) if ng else set(); p+=1; words.append((wt,d,forms,good))
    return nW,words
class Sys:
    def __init__(s, piv=None): s.piv=dict(piv) if piv else {}; s.mask=0
    def red(s,m,c):
        pm=s.mask
        while m & pm:
            h=(m & pm).bit_length()-1; a,b=s.piv[h]; m^=a; c^=b
        return m,c
    def add(s,m,c):
        m,c=s.red(m,c)
        if m==0: return c==0
        h=m.bit_length()-1
        for k,(a,b) in list(s.piv.items()):
            if (a>>h)&1: s.piv[k]=(a^m,b^c)
        s.piv[h]=(m,c); s.mask|=1<<h; return True
    def copy(s):
        t=Sys(s.piv); t.mask=s.mask; return t
def analyse(S, word):
    wt,d,forms,good=word
    red=[S.red(m,c) for (m,c) in forms]
    basis=[]; rel=[]
    for t,(m,c) in enumerate(red):
        v,comb,par=m,1<<t,c
        for (bv,bc,bp) in basis:
            if v & (bv & -bv): v^=bv; comb^=bc; par^=bp
        if v: basis.append((v,comb,par))
        else: rel.append((comb,par))
    ach=[g for g in good if all((pc(g&comb)&1)==par for comb,par in rel)]
    return red, ach, len(basis)
nodes=0
def search(S, words, depth):
    global nodes; nodes+=1
    while True:
        changed=False; best=None
        for q,w in enumerate(words):
            red,ach,rk=analyse(S,w)
            if not ach: return 0
            if rk==0: continue
            if len(ach)==1:
                g=ach[0]
                for t,(m,c) in enumerate(red):
                    if m and not S.add(m,((g>>t)&1)^c): return 0
                changed=True
            elif best is None or len(ach)<best[0]: best=(len(ach),q,red,ach)
        if not changed: break
    if best is None:
        free=NWG-len(S.piv)
        if free==0:
            w=0
            for h,(a,b) in S.piv.items():
                assert a==1<<h
                if b: w|=1<<h
            print(f'SOLUTION w={w:x} depth {depth}', flush=True)
        else: print(f'SOLUTION FAMILY at depth {depth}: {free} free variables', flush=True)
        return 1
    n,q,red,ach=best; found=0
    for g in ach:
        T=S.copy(); ok=True
        for t,(m,c) in enumerate(red):
            if m and not T.add(m,((g>>t)&1)^c): ok=False; break
        if ok: found+=search(T, words, depth+1)
    return found
for fn in sys.argv[1:]:
    nW,words=parse(fn); t0=time.time(); nodes=0; NWG=nW
    # most restrictive words first speeds up conflict detection
    words.sort(key=lambda w: len(w[3])/(1<<w[1]))
    f=search(Sys(), words, 0)
    print(fn.split('/')[-1], 'NW', nW, 'result', 'UNSAT (exhaustive)' if f==0 else f'SAT families {f}', 'nodes', nodes, f'time {time.time()-t0:.0f}s', flush=True)
