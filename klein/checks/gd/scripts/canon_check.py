import sys, re, hashlib, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0,HERE + '/../scripts')
exec(open(HERE + '/../scripts/aut_xcheck.py').read().split("codes=load()\nref=")[0])
codes=load()
hs={}
for ci,G in enumerate(codes):
    W=span(G); w8=[w for w in W if pc(w)==8]; w10=[w for w in W if pc(w)==10]
    words=w8+w10
    out=dread(words, canon=True)
    # keep only canonical graph adjacency lines "  v : nbrs;" after the automorphism output
    lines=[l for l in out.split('\n') if re.match(r'^\s*\d+\s*:', l)]
    # adjacency lines may wrap; join continuation lines
    txt=out[out.find('\n   0 :') if '\n   0 :' in out else out.find(' 0 :'):]
    txt=re.sub(r'cpu time.*','',txt)
    h=hashlib.md5(re.sub(r'\s+',' ',txt).encode()).hexdigest()
    hs.setdefault(h,[]).append(ci)
    if ci==0: print(out[:300]); print('...'); print(txt[:200])
print('distinct',len(hs)); print([v for v in hs.values() if len(v)>1])
