"""Independent check of the 41 codes, |Aut(Y)| and fpf-involution class counts.
Own parsing of dreadnaut output; group order from generators by own BFS (Schreier-Sims not needed for |G|<=1e6);
compare with nauty grpsize and with classes.pkl."""
import sys, subprocess, pickle, itertools, hashlib, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
M=36
def load():
    blocks=open(HERE + '/../../../codes36.txt').read().strip().split('\n\n')
    out=[]
    for b in blocks:
        rows=[l.strip() for l in b.strip().split('\n') if l.strip()]
        out.append([int(r[::-1],2) for r in rows])
    return out
def pc(x): return bin(x).count('1')
def span(G):
    S=[0]
    for g in G: S=S+[s^g for s in S]
    return S
def rank(vs):
    piv={}
    for v in vs:
        while v:
            h=v.bit_length()-1
            if h in piv: v^=piv[h]
            else: piv[h]=v; break
    return len(piv)
def dread(words, canon=False):
    nv=M+len(words)
    adj=[[] for _ in range(M)]
    for k,w in enumerate(words):
        for i in range(M):
            if (w>>i)&1: adj[i].append(M+k)
    txt=f'n={nv} g\n'+'\n'.join(' '.join(map(str,a))+';' for a in adj)+'\n.\n'
    txt+=f'f=[0:{M-1}|{M}:{nv-1}]\n'
    txt+=('c x b\n' if canon else '+a x\n')
    txt+='q\n'
    out=subprocess.run(['dreadnaut'],input=txt,capture_output=True,text=True).stdout
    return out
def parse_gens(out):
    # generator lines: start with '(' ; continuation lines are indented with '(' or digits
    lines=out.split('\n'); gens=[]; cur=None
    for line in lines:
        if line.startswith('('):
            if cur is not None: gens.append(cur)
            cur=line.strip()
        elif cur is not None and line.startswith('   ') and line.strip() and (line.strip()[0] in '(0123456789'):
            cur+=' '+line.strip()
        else:
            if cur is not None: gens.append(cur); cur=None
    if cur is not None: gens.append(cur)
    perms=[]
    for g in gens:
        p=list(range(10**6 if False else 0))
        mp={}
        for cyc in re.findall(r'\(([^)]*)\)', g):
            els=[int(x) for x in cyc.split()]
            for a,b in zip(els, els[1:]+els[:1]): mp[a]=b
        perms.append([mp.get(i,i) for i in range(M)])
    m=re.search(r'grpsize=([0-9.e+]+)', out.replace(' ',''))
    gs=None
    mm=re.search(r'grpsize=([^;]+);', out)
    if mm: gs=mm.group(1).strip()
    return perms, gs
def apply(p,w):
    o=0
    for i in range(M):
        if (w>>i)&1: o|=1<<p[i]
    return o
def gorder(gens):
    idp=tuple(range(M)); seen={idp}; fr=[idp]
    while fr:
        nf=[]
        for p in fr:
            for g in gens:
                q=tuple(g[p[i]] for i in range(M))
                if q not in seen: seen.add(q); nf.append(q)
        fr=nf
    return seen
def fpf_classes(G, gens):
    invs=[p for p in G if all(p[p[i]]==i and p[i]!=i for i in range(M))]
    done=set(); ncl=0; sizes=[]
    for t in invs:
        if t in done: continue
        ncl+=1; cls={t}; fr=[t]
        while fr:
            nf=[]
            for x in fr:
                for g in gens:
                    gi=[0]*M
                    for i in range(M): gi[g[i]]=i
                    c=tuple(g[x[gi[i]]] for i in range(M))   # g x g^-1
                    if c not in cls: cls.add(c); nf.append(c)
            fr=nf
        done|=cls; sizes.append(len(cls))
    return len(invs), ncl, sizes
codes=load()
ref=pickle.load(open(HERE + '/../../../model/classes.pkl','rb'))
assert len(codes)==41
canon=set(); tot=0; problems=[]
for ci,G in enumerate(codes):
    assert len(G)==18 and rank(G)==18
    W=span(G); Wset=set(W)
    assert all(pc(a&b)%2==0 for a in G for b in G)
    d=min(pc(w) for w in W if w); assert d==8,(ci,d)
    wd=[0]*37
    for w in W: wd[pc(w)]+=1
    w8=[w for w in W if pc(w)==8]; w10=[w for w in W if pc(w)==10]
    words=w8 if rank(w8)==18 else w8+w10
    assert rank(words)==18
    out=dread(words)
    gens,gs=parse_gens(out)
    valid=[p for p in gens if all(apply(p,g) in Wset for g in G)]
    Gr=gorder(valid) if valid else {tuple(range(M))}
    ninv,ncl,sizes=fpf_classes(Gr, valid)
    # canonical form for inequivalence
    outc=dread(words, canon=True)
    h=hashlib.md5(outc.split('canupdates')[0].encode() if False else re.sub(r'^.*?\n(?=\s*0 :)', '', outc, flags=re.S).encode()).hexdigest()
    canon.add(h)
    r=ref[ci]
    flag='' if (len(Gr),ninv,ncl)==(r[1],r[2],r[3]) and float(gs)==len(Gr) and len(valid)==len(gens) else ' <-- MISMATCH'
    if flag: problems.append(ci)
    tot+=ncl
    print(ci, 'A8',wd[8],'A10',wd[10],'rank8',rank(w8),'nauty grpsize',gs,'gens',len(gens),'valid',len(valid),'|G|',len(Gr),'fpf inv',ninv,'classes',ncl,'ref',r[1:],flag, flush=True)
print('total classes',tot,'distinct canonical forms',len(canon),'problems',problems)
