#!/bin/bash
# Y22 exhaustive search, RESUMABLE. Usage: ./run.sh NPROC
# Each invocation starts a new attempt out/att_<a>/ that searches exactly the reps of xreps22.txt which have no
# complete result line ('W x ...' with 7 fields) in any earlier attempt; lines are dealt round-robin to NPROC
# processes at nice 10. After a preemption just run ./run.sh NPROC again. 'ALL_DONE' appears in out/all_done.txt
# when an attempt finds nothing left to do (run it once more after the last attempt to confirm).
set -e
cd "$(dirname "$0")"
N=$1
[ -n "$N" ] || { echo "usage: ./run.sh NPROC"; exit 1; }
mkdir -p out tmp
export TMPDIR=$PWD/tmp
a=0; while [ -d out/att_$a ]; do a=$((a+1)); done
mkdir out/att_$a
cat out/att_*/w_*.txt 2>/dev/null | awk '$1=="W" && NF==7 {print $2}' | sort -u > out/att_$a/done_before.txt
awk -v df=out/att_$a/done_before.txt 'BEGIN{while ((getline l < df) > 0) d[l]=1} !($2 in d)' xreps22.txt > out/att_$a/todo.txt
n=$(wc -l < out/att_$a/todo.txt)
ndone=$(awk -v df=out/att_$a/done_before.txt 'BEGIN{while ((getline l < df) > 0) d[l]=1} ($2 in d){c++} END{print c+0}' xreps22.txt)
ntot=$(wc -l < xreps22.txt)
echo "attempt $a: $ndone of $ntot reps done before, $n to do, $N processes, $(date -u)" | tee out/att_$a/info.txt
if [ $((ndone + n)) -ne "$ntot" ]; then echo "INCONSISTENT COUNTS" | tee -a out/att_$a/info.txt; exit 2; fi
if [ "$n" -eq 0 ]; then echo "ALL_DONE $ntot reps $(date -u)" > out/all_done.txt; exit 0; fi
for ((ch=0; ch<N; ch++)); do
  nice -n 10 ./engine9 sep_I28b.eng wsearch xactionK_b2.bin out/att_$a/todo.txt 31 10 $N $ch > out/att_$a/w_$ch.txt 2> out/att_$a/w_$ch.err &
done
wait
echo "attempt $a finished $(date -u)" >> out/att_$a/info.txt
