#!/bin/bash
# profrun.sh SRC CODE SPL NPART PART TAG : PC-sampling profile of SRC on one part; prints level shares and top source lines
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp
SRC=$1; CODE=$2; SPL=$3; NPART=$4; PART=$5; TAG=$6; D=<HOME>/c72/explore/runs2/$CODE
gcc -pipe -O3 -g -no-pie -fno-pie -D_GNU_SOURCE -DPROFPC -march=x86-64-v4 -mavx512vbmi -mgfni -mavx512vpopcntdq -o bin/prof_$TAG $SRC || exit 1
PROFOUT=logs/dev/prof_$TAG.pc LTSHFILE=$D/sym.ltsh nice -n 10 bin/prof_$TAG $D/inst.txt $SPL $NPART $PART > logs/dev/prof_$TAG.log 2> logs/dev/prof_$TAG.err
cat logs/dev/prof_$TAG.err
sort logs/dev/prof_$TAG.pc | uniq -c | sort -rn | head -600 > logs/dev/prof_${TAG}_top.txt
python3 - "$TAG" "$SRC" << 'PY'
import subprocess, collections, sys
tag, src = sys.argv[1], sys.argv[2]
top = [l.split() for l in open(f'logs/dev/prof_{tag}_top.txt')]
allc = sum(1 for _ in open(f'logs/dev/prof_{tag}.pc'))
out = subprocess.run(['addr2line', '-e', f'bin/prof_{tag}', '-s', '-i'] + [a for _, a in top], capture_output=True, text=True).stdout.split('\n')
# with -i, each address may print several lines (inline chain); use the last line before the next address: rerun without -i for simplicity
out = subprocess.run(['addr2line', '-e', f'bin/prof_{tag}', '-s'] + [a for _, a in top], capture_output=True, text=True).stdout.split('\n')
lines = open(src).read().split('\n')
byline = collections.Counter()
for (n, a), ln in zip(top, out): byline[ln] += int(n)
print('samples', allc)
for ln, n in byline.most_common(30):
    k = ln.split(':')[1].split()[0] if ':' in ln and ln.split(':')[0] == src.split('/')[-1] else None
    txt = lines[int(k) - 1].strip()[:110] if k and k.isdigit() else ''
    print(f'{100*n/allc:5.1f}% {ln:40s} {txt}')
PY
