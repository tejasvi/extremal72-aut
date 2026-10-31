import glob, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
D=HERE + '/../planted'
def sols(fn):
    s=[]
    for l in open(fn):
        if l.startswith('SOLUTION w='): s.append(int(l.split('=')[1],16))
    return s
def done(fn):
    t=open(fn).read()
    return 'DONE result=COMPLETE' in t, 'LEAF' in t
tot=ok=0
for T in sorted(glob.glob(D+'/*.txt')):
    base=T[:-4]
    if not os.path.exists(base+'.brute') or 'BRUTE nsol' not in open(base+'.brute').read(): continue
    parts23=[base+f'.split2_3_{p}' for p in range(3)]; parts45=[base+f'.split4_5_{p}' for p in range(5)]
    files=[base+'.nosplit']+parts23+parts45
    if not all(os.path.exists(f) and done(f)[0] for f in files): continue
    br=set(sols(base+'.brute')); assert len(br)==len(sols(base+'.brute'))
    pl=set(int(l,16) for l in open(T+'.planted') if l.strip())
    ns=sols(base+'.nosplit')
    s23=[x for f in parts23 for x in sols(f)]; s45=[x for f in parts45 for x in sols(f)]
    leaf=any(done(f)[1] for f in files)
    good = pl<=br and set(ns)==br and len(ns)==len(set(ns)) and set(s23)==br and set(s45)==br and not leaf
    tot+=1; ok+=good
    print(('OK  ' if good else 'FAIL'), os.path.basename(base), f'planted {len(pl)} brute {len(br)} nosplit {len(ns)} split23 {len(s23)}/{len(set(s23))} split45 {len(s45)}/{len(set(s45))} leaf {leaf}')
print(f'TOTAL {tot} OK {ok}')
