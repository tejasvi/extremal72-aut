#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
D=$KLEIN/checks/gd
for T in v4_18_4_v4gd4_s1_f41_p3_r0_fl2 v4_18_4_v4gd4_s4_f41_p3_r0_fl2 v4_23_4_v4gd4_s1_f42_p3_r0_fl0; do
  ./v4gd4dbg $D/pinned/$T.txt.pin.txt 14 search 1 -1 1 0 0 1 > $T.dbg4.out 2> $T.dbg4.err
  a=$(grep -o "nodes [0-9]*" $T.dbg4.out); b=$(grep -o "nodes [0-9]*" $D/pinned/$T.nosplit)
  s1=$(grep SOLUTION $T.dbg4.out | sort | md5sum | cut -c1-8); s2=$(grep SOLUTION $D/pinned/$T.nosplit | sort | md5sum | cut -c1-8)
  echo "$T dbg4: $a vs orig: $b; sols $s1 vs $s2; $(tail -n 1 $T.dbg4.err)"
done
for I in 18_4 32_1 3_3 20_8; do
  ./v4gd4dbg $KLEIN/gd_runs/inst/v4_$I.txt 14 search 1 -1 1 0 0 1 > real4_$I.dbg.out 2> real4_$I.dbg.err
  echo "real $I nosplit: $(grep DONE real4_$I.dbg.out) ; $(grep DBG real4_$I.dbg.err | tail -n 1)"
done
