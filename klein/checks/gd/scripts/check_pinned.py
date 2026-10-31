import sys, re, os
T=sys.argv[1]
free=list(map(int,open(T+'.txt.free').read().split()))
def red(w):
    r=0
    for k,t in enumerate(free):
        if (w>>t)&1: r|=1<<k
    return r
def sols(fn):
    t=open(fn).read()
    h=re.search(r'hist:(.*)',t)
    return [int(x,16) for x in re.findall(r'SOLUTION w=([0-9a-f]+)',t)], 'DONE result=COMPLETE' in t, 'LEAF' in t, ({int(a.split(':')[0]):int(a.split(':')[1]) for a in h.group(1).split()} if h else {})
br=[int(x,16) for x in re.findall(r'SOLUTION w=([0-9a-f]+)',open(T+'.brute').read())]
pl=set(int(l,16) for l in open(T+'.txt.planted') if l.strip())
ns,dn,lf,hn=sols(T+'.nosplit')
res=[]; ok=dn and not lf and set(br)==set(red(w) for w in ns) and len(ns)==len(set(ns)) and pl<=set(br)
hi=sum(1 for w in ns if w>>64)
for (sd,np_) in [(2,3),(3,4),(5,16)]:
    P=[sols(T+f'.split{sd}_{np_}_{p}') for p in range(np_)]
    allp=[x for q in P for x in q[0]]
    good=all(q[1] and not q[2] for q in P) and set(red(w) for w in allp)==set(br)
    acc=all(P[q][3].get(dd,0)==hn.get(dd,0) for q in range(np_) for dd in range(sd+1)) and all(sum(P[q][3].get(dd,0) for q in range(np_))==hn.get(dd,0) for dd in range(sd+1,90))
    ok=ok and good and acc
    res.append(f'split{sd}/{np_}: sols {len(allp)}/{len(set(allp))} acc {acc}')
print(('OK  ' if ok else 'FAIL'), os.path.basename(T), f'planted {len(pl)} brute {len(br)} nosplit {len(ns)} (with bit>=64: {hi}) maxdepth {max(hn) if hn else None}', ' | '.join(res))
