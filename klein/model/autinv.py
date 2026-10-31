"""For each of the 41 self-dual [36,18,8] codes: automorphism group generators via nauty (graph: coordinates vs
words of weight 8 [and 10 if needed]), then involutions alpha in Aut(D) and the dimension of the fixed subcode."""
import sys, subprocess, itertools, random, pickle, os
HERE = os.path.dirname(os.path.abspath(__file__))
def load():
    blocks=open(HERE + '/../codes36.txt').read().strip().split('\n\n')
    codes=[]
    for b in blocks:
        rows=[l.strip() for l in b.strip().split('\n') if l.strip()]
        codes.append([sum(int(ch)<<j for j,ch in enumerate(r)) for r in rows])
    return codes
def span(G):
    S=[0]
    for g in G: S=S+[s^g for s in S]
    return S
def rank(vs):
    basis=[]
    for v in vs:
        for b in basis: v=min(v,v^b)
        if v: basis.append(v)
    return len(basis)
def apply(perm,w):
    out=0
    for i in range(36):
        if (w>>i)&1: out|=1<<perm[i]
    return out
def compose(p,q):  # first p then q
    return [q[p[i]] for i in range(36)]
def order(p):
    seen=[False]*36; o=1
    from math import gcd
    for i in range(36):
        if not seen[i]:
            l=0; j=i
            while not seen[j]: seen[j]=True; j=p[j]; l+=1
            o=o*l//gcd(o,l)
    return o
def power(p,e):
    r=list(range(36)); b=p[:]
    while e:
        if e&1: r=compose(r,b)
        b=compose(b,b); e>>=1
    return r
def nauty_gens(words):
    nv=36+len(words)
    lines=[f'n={nv} g']
    adj=[[] for _ in range(nv)]
    for k,w in enumerate(words):
        for i in range(36):
            if (w>>i)&1: adj[i].append(36+k)
    for i in range(36):
        lines.append(' '.join(map(str,adj[i]))+(';' if i<nv-1 else '.'))
    for v in range(36,nv-1): lines.append(';')
    lines.append('.')
    txt='\n'.join(lines)
    # partition: coordinates | words
    txt+=f'\nf=[0:35|36:{nv-1}]\nx\n'
    out=subprocess.run(['dreadnaut'],input=txt,capture_output=True,text=True).stdout
    gens=[]; cur=None
    grpsize=None
    for line in out.split('\n'):
        s=line.strip()
        if line.startswith('('):
            if cur is not None: gens.append(cur)
            cur=s
        elif cur is not None and line.startswith(' ') and s and (s[0]=='(' or s[0].isdigit()):
            cur+=' '+s
        else:
            if cur is not None: gens.append(cur); cur=None
        if 'grpsize' in s: grpsize=s.split(';')[1].strip()
    if cur is not None: gens.append(cur)
    perms=[]
    for g in gens:
        p=list(range(nv))
        for cyc in g.replace(')',')|').split('|'):
            cyc=cyc.strip()
            if not cyc: continue
            els=[int(x) for x in cyc.strip('()').split()]
            for a,b in zip(els,els[1:]+els[:1]): p[a]=b
        perms.append(p[:36])
    return perms,grpsize
if __name__=='__main__':
    codes=load(); res=[]
    for ci,G in enumerate(codes):
        W=span(G); Wset=set(W)
        words=[w for w in W if bin(w).count('1')==8]
        if rank(words)<18: words+= [w for w in W if bin(w).count('1')==10]
        perms,gs=nauty_gens(words)
        perms=[p for p in perms if all(apply(p,g) in Wset for g in G)]
        # collect involutions from random products
        invs={}
        rnd=random.Random(ci)
        cand=perms[:]
        for _ in range(400):
            if not perms: break
            p=list(range(36))
            for _ in range(rnd.randint(1,6)): p=compose(p,rnd.choice(perms))
            cand.append(p)
        for p in cand:
            o=order(p)
            if o%2==0:
                a=power(p,o//2)
                if all(apply(a,g) in Wset for g in G):
                    fixed=sum(1 for i in range(36) if a[i]==i)
                    invs[tuple(a)]=fixed
        # fixed subcode dimension: D(alpha) = {d : alpha d = d}
        best=None
        for a,f in invs.items():
            a=list(a)
            fixv=[w for w in [g ^ apply(a,g) for g in G]]
            # dim D(alpha) = 18 - rank of (alpha - I) on D
            k=18-rank(fixv)
            if best is None or k<best[0]: best=(k,f,a)
        print(ci, gs, 'gens',len(perms),'involutions found',len(invs),'best dim D(alpha)=',best[0] if best else None,'fixed points',best[1] if best else None, flush=True)
        res.append(dict(code=G,perms=perms,best=best))
    pickle.dump(res,open(HERE + '/invs.pkl','wb'))
