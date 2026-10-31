#!/bin/bash
# valstd.sh CODE : standard check_box part (SPL from PLAN.txt, part 17 of 200000): lwe8 output cached in logs/val/std/,
# frozen/lwe11 compared on LEVEL/DONE/SOLUTION lines; probe estimate compared with PLAN.txt.  Appends to logs/val/STD_SUMMARY.txt
set -u
cd <HOME>/c72/c2opt/alg; export TMPDIR=<HOME>/c72/c2opt/alg/tmp; mkdir -p logs/val/std
C=$1; D=<HOME>/c72/explore/runs2/$C; SPL=$(grep '^SPLIT_LEVEL ' $D/PLAN.txt | awk '{print $2}')
[ -s logs/val/std/${C}_lwe8.log ] && grep -q '^DONE' logs/val/std/${C}_lwe8.log || src/runpart.sh bin/lwe8 $C $SPL 200000 17 logs/val/std/${C}_lwe8
src/runpart.sh frozen/lwe11 $C $SPL 200000 17 logs/val/std/${C}_lwe11
A=$(grep -E '^LEVEL|^DONE|^SOL' logs/val/std/${C}_lwe8.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
B=$(grep -E '^LEVEL|^DONE|^SOL' logs/val/std/${C}_lwe11.log | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16)
EXP=$(grep '^PROBE_LTS ' $D/PLAN.txt | awk '{print $2}'); GOT=$(PROBES=20000 LTSHFILE=$D/sym.ltsh nice -n 10 frozen/lwe11 $D/inst.txt | tail -1 | awk '{print $NF}')
echo "$C spl $SPL part 17/200000 lwe8 $A lwe11 $B $([ $A = $B ] && echo IDENTICAL || echo DIFFER) probe plan $EXP lwe11 $GOT $([ "$EXP" = "$GOT" ] && echo PROBE_OK || echo PROBE_MISMATCH) user_s lwe8 $(cut -d' ' -f1 logs/val/std/${C}_lwe8.time) lwe11 $(cut -d' ' -f1 logs/val/std/${C}_lwe11.time) bin $(sha256sum frozen/lwe11 | cut -c1-16)" >> logs/val/STD_SUMMARY.txt
