#!/bin/bash
# proflev.sh BIN LEVEL INST SPL NPART PART TAG [LTSH] [LTSB] : PC profile restricted to one level; function and line shares
cd <HOME>/c72/c2opt/alg/prof; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
BIN=$1; LEV=$2; INST=$3; SPL=$4; NP=$5; PT=$6; TAG=$7
env PROFLEV=$LEV PROFOUT=$TAG.pc ${8:+LTSHFILE=$8} ${9:+LTSBFILE=$9} nice -n 10 $BIN $INST $SPL $NP $PT > $TAG.log 2> $TAG.err
grep "PROF level" $TAG.err | tr '\n' ' '; echo
sort $TAG.pc | uniq -c | sort -rn > ${TAG}_top.txt
<HOME>/c72/venv/bin/python -I - $BIN $TAG << 'PY'
import subprocess, collections, sys
binp, tag = sys.argv[1], sys.argv[2]
top = [l.split() for l in open(f'{tag}_top.txt')]
tot = sum(int(n) for n, _ in top)
out = subprocess.run(['addr2line', '-f', '-e', binp] + [a for _, a in top], capture_output=True, text=True).stdout.split('\n')
funcs = collections.Counter()
for i, (n, a) in enumerate(top): funcs[out[2 * i]] += int(n)
print(f'samples {tot}:', ', '.join(f'{f} {100*n/tot:.1f}%' for f, n in funcs.most_common(9)))
PY
