#!/bin/bash
# aggregate the job logs of both machines (hostA/, hostB/ next to this script)
# (the original version of this script first copied the res/ directories from the two machines)
cd "$(dirname "$0")"
python3 - << 'PY'
import glob, re, collections
files = glob.glob('host[AB]/r*_p*.err')
done = {}; 
tot = collections.defaultdict(lambda: [0]*8); sols=0; missing=[]
for r in range(7):
    for p in range(32):
        fs=[f for f in files if f.endswith(f'/r{r}_p{p}.err')]
        ok=False
        for f in fs:
            s=open(f).read()
            m=re.search(r'rep (\d+) u1=(\w+) \|L1\|=(\d+) nodes: ([\d ]+) sols=(\d+)', s)
            if m and 'TOTAL solutions' in s:
                ok=True
                cnt=list(map(int,m.group(4).split()))
                for d in range(7): tot[r][d+1]+=cnt[d]
                sols+=int(m.group(5))
        if not ok: missing.append((r,p))
print("parts complete:", 7*32-len(missing), "/", 7*32)
for r in range(7):
    print("rep",r,"nodes per depth (depth-1 row fixed => n1 counts parts):", tot[r][2:])
allt=[sum(tot[r][d] for r in range(7)) for d in range(8)]
print("ALL reps, nodes at depth 2..7:", allt[2:])
outs=glob.glob('host[AB]/r*_p*.out')
nsol=sum(1 for f in outs for line in open(f) if line.startswith('SOLUTION'))
print("solutions reported:", sols, " SOLUTION lines:", nsol)
if missing: print("missing parts:", missing[:20], '...' if len(missing)>20 else '')
PY
