#!/bin/bash
# Y23 join search on the box, RESUMABLE. Usage: ./run.sh NPROC [LIST]   (LIST default todo_box1.txt)
# Each call = new attempt out/att_<a>/ over the reps of LIST that have no complete 'J' line (10 fields) in any
# earlier attempt; round-robin over NPROC processes at nice 10, ulimit -v 1 GiB per process.
set -e
cd "$(dirname "$0")"
N=$1; LIST=${2:-todo_box1.txt}
[ -n "$N" ] || { echo "usage: ./run.sh NPROC [LIST]"; exit 1; }
[ "$N" -ge 1 ] 2>/dev/null && [ "$N" -le 380 ] || { echo "NPROC must be 1..380"; exit 1; }   # guard against process explosions
mkdir -p out tmp
export TMPDIR=$PWD/tmp
a=0; while [ -d out/att_$a ]; do a=$((a+1)); done
mkdir out/att_$a
cat out/att_*/j_*.txt 2>/dev/null | awk '$1=="J" && NF==10 {print $2}' | sort -u > out/att_$a/done_before.txt
awk -v df=out/att_$a/done_before.txt 'BEGIN{while ((getline l < df) > 0) d[l]=1} !($2 in d)' $LIST > out/att_$a/todo.txt
n=$(wc -l < out/att_$a/todo.txt)
ndone=$(awk -v df=out/att_$a/done_before.txt 'BEGIN{while ((getline l < df) > 0) d[l]=1} ($2 in d){c++} END{print c+0}' $LIST)
ntot=$(wc -l < $LIST)
echo "attempt $a: $ndone of $ntot reps of $LIST done before, $n to do, $N processes, $(date -u)" | tee out/att_$a/info.txt
if [ $((ndone + n)) -ne "$ntot" ]; then echo "INCONSISTENT COUNTS" | tee -a out/att_$a/info.txt; exit 2; fi
if [ "$n" -eq 0 ]; then echo "ALL_DONE $ntot reps of $LIST $(date -u)" > out/all_done.txt; exit 0; fi
ulimit -v 1048576
for ((ch=0; ch<N; ch++)); do
  nice -n 10 ./engine9 sep_A2.eng join out/att_$a/todo.txt 36 70 104 $N $ch > out/att_$a/j_$ch.txt 2> out/att_$a/j_$ch.err &
done
wait
echo "attempt $a finished $(date -u)" >> out/att_$a/info.txt
