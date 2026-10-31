#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
# node accounting on a real instance: nosplit vs all 16 production parts (split 5); usage: acct.sh INST SOLVER
I=$1; SOLV=$2; D=$KLEIN/checks/gd/acct
$KLEIN/gd_runs/$SOLV $KLEIN/gd_runs/inst/v4_$I.txt 14 search 1 -1 1 0 0 1 > $D/${I}_nosplit 2>/dev/null
for p in $(seq 0 15); do $KLEIN/gd_runs/$SOLV $KLEIN/gd_runs/inst/v4_$I.txt 14 search 1 5 16 $p 0 1 > $D/${I}_part$p 2>/dev/null; done
python3 - $I <<'PY'
import sys, re
I=sys.argv[1]; D='$KLEIN/checks/gd/acct'
def H(fn):
    t=open(fn).read(); h=re.search(r'hist:(.*)',t).group(1).split()
    return {int(a.split(':')[0]):int(a.split(':')[1]) for a in h}, ('COMPLETE' in t and ' sols 0 ' in t)
hn,okn=H(f'{D}/{I}_nosplit'); P=[H(f'{D}/{I}_part{p}') for p in range(16)]
acc=all(P[q][0].get(d,0)==hn.get(d,0) for q in range(16) for d in range(6)) and all(sum(P[q][0].get(d,0) for q in range(16))==hn.get(d,0) for d in range(6,80))
box={}
for l in open('$KLEIN/checks/gd/box_out_summary2.txt'):
    r=l.rstrip('\n').split('|')
    if r[0].startswith(f'v4_{I}_') and r[3].startswith('DONE'): box[int(r[0].split('_')[-1])]=r[4]
same=all(open(f'{D}/{I}_part{p}').read().split('hist:')[1].strip()==box[p].split('hist:')[1].strip() for p in box)
print(f'{I}: nosplit nodes {sum(hn.values())} maxdepth {max(hn)}; all parts COMPLETE sols 0: {okn and all(q[1] for q in P)}; accounting exact: {acc}; box parts compared {len(box)} identical: {same}')
PY
