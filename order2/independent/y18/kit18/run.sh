#!/bin/bash
# run.sh NPROC: resumable work-queue run. Requeues chunks left in running/ by an earlier start, then runs NPROC joinq
# workers (nice 10, ulimit -v 1 GiB); each claims chunks by atomic rename. ALL_DONE in all_done.txt when queue and
# running are empty at the end.
cd "$(dirname "$0")"
N=$1
[ "$N" -ge 1 ] && [ "$N" -le 380 ] || { echo "NPROC must be 1..380"; exit 1; }
export TMPDIR=$PWD/tmp
for f in running/*; do [ -e "$f" ] || continue; b=$(basename $f); mv "$f" "queue/${b%.*}"; done
echo "start $(date -u): queue $(ls queue | wc -l) done $(ls done | wc -l) workers $N" >> run_status.log
ulimit -v 1048576
for ((w=0; w<N; w++)); do
  nice -n 10 ./engine15 sep_A2.eng joinq . 36 70 104 $w > /dev/null 2> tmp/worker_$w.err &
done
wait
nq=$(ls queue | wc -l); nr=$(ls running | wc -l); nd=$(ls done | wc -l)
echo "end $(date -u): queue $nq running $nr done $nd" >> run_status.log
if [ $nq -eq 0 ] && [ $nr -eq 0 ]; then echo "ALL_DONE $(date -u) chunks $nd" > all_done.txt; fi
