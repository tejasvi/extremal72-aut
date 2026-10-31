import sys, re
T=sys.argv[1]
def pc(x): return bin(x).count('1')
L=open(T+'.txt').read().split('\n'); nW,nw=map(int,L[0].split()); p=1; words=[]
for _ in range(nw):
    wt,d,ng=map(int,L[p].split()); p+=1; forms=[]
    for t in range(d):
        m,c=L[p].split(); p+=1; forms.append((int(m,16),int(c)))
    good=set(map(int,L[p].split())) if ng else set(); p+=1; words.append((forms,good))
def genuine(w):
    for forms,good in words:
        g=0
        for t,(m,c) in enumerate(forms): g|=((pc(m&w)&1)^c)<<t
        if g not in good: return False
    return True
def sols(fn):
    t=open(fn).read(); return [int(x,16) for x in re.findall(r'SOLUTION w=([0-9a-f]+)',t)], ('DONE result=COMPLETE' in t), ('LEAF' in t), re.search(r'hist:(.*)',t).group(1).split() if 'hist:' in t else []
pl=[int(l,16) for l in open(T+'.txt.planted') if l.strip()]
ns,dn,lf,hn=sols(T+'.nosplit')
parts=[sols(T+f'.part{q}') for q in range(16)]
allp=[x for q in parts for x in q[0]]
ok=dn and all(q[1] for q in parts) and not lf and not any(q[2] for q in parts)
ok=ok and set(pl)<=set(ns) and set(pl)<=set(allp) and set(ns)==set(allp)
extra=set(ns)-set(pl)
gen_ok=all(genuine(w) for w in set(ns)|set(allp))
# node accounting: depth<=5 identical in each part; depth>5 sums equal nosplit
H=lambda h: {int(a.split(':')[0]):int(a.split(':')[1]) for a in h}
hn=H(hn); hp=[H(q[3]) for q in parts]
acc=all(hp[q].get(dd,0)==hn.get(dd,0) for q in range(16) for dd in range(0,6)) and all(sum(hp[q].get(dd,0) for q in range(16))==hn.get(dd,0) for dd in range(6,80))
print(('OK  ' if ok and gen_ok and acc else 'FAIL'), T.split('/')[-1], f'planted {len(pl)} (bits>=64 set in {sum(1 for w in pl if w>>64)}) nosplit {len(ns)} parts total {len(allp)} distinct {len(set(allp))} extra {len(extra)} all genuine {gen_ok} node-accounting {acc} maxdepth {max(hn) if hn else None}')
