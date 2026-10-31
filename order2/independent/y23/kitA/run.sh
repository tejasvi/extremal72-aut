#!/bin/bash
# Y23 box part (todo_box1.txt = 936951 reps), join mode with a work queue, RESUMABLE. Usage: ./run.sh NPROC
# Queue (in list order; heavy reps are scattered): first 95% of the reps in chunks of 100, next 4% in chunks of 10,
# last 1% one per chunk (short chunks at the end keep the tail short). Workers (engine10 joinq) claim chunks by atomic
# rename, smallest name first; outputs out/<chunk>.out. After an interruption run ./run.sh NPROC again: chunks left
# in running/ are requeued (their partial output is redone).
set -e
cd "$(dirname "$0")"
N=$1
[ -n "$N" ] || { echo "usage: ./run.sh NPROC"; exit 1; }
[ "$N" -ge 1 ] 2>/dev/null && [ "$N" -le 380 ] || { echo "NPROC must be 1..380"; exit 1; }   # guard against process explosions
export TMPDIR=$PWD/tmp
mkdir -p tmp queue running done out
if [ ! -f queue_prepared ]; then
  T=$(wc -l < todo_box1.txt); A=$((T * 95 / 100)); B=$((T * 99 / 100))
  head -n $A todo_box1.txt | split -l 100 -d -a 6 - queue/a
  sed -n "$((A + 1)),${B}p" todo_box1.txt | split -l 10 -d -a 6 - queue/b
  tail -n +$((B + 1)) todo_box1.txt | split -l 1 -d -a 6 - queue/c
  cat queue/* | wc -l > tmp/queued_lines.txt
  [ "$(cat tmp/queued_lines.txt)" = "$(wc -l < todo_box1.txt)" ] || { echo "QUEUE SIZE MISMATCH"; exit 2; }
  touch queue_prepared
fi
for f in running/*; do [ -e "$f" ] || continue; b=$(basename "$f"); mv "$f" "queue/${b%.*}"; done
echo "start $(date -u): queue $(ls queue | wc -l) done $(ls done | wc -l) workers $N" >> run_status.log
ulimit -v 1048576
for ((w=0; w<N; w++)); do
  nice -n 10 ./engine10 sep_A2.eng joinq . 36 70 104 $w > /dev/null 2> tmp/worker_$w.err &
done
wait
nq=$(ls queue | wc -l); nr=$(ls running | wc -l); nd=$(ls done | wc -l)
echo "end $(date -u): queue $nq running $nr done $nd" >> run_status.log
if [ $nq -eq 0 ] && [ $nr -eq 0 ]; then echo "ALL_DONE $(date -u) chunks $nd" > all_done.txt; fi
