#!/bin/bash
KLEIN="$(cd "$(dirname "$0")/../../.." && pwd)"; export KLEIN
D=$KLEIN/checks/gd
for T in v4_29_0_v4gd3_s1_f40_p3_r0_fl2 v4_29_0_v4gd3_s2_f40_p3_r0_fl2 v4_5_0_v4gd3_s1_f40_p4_r0_fl0; do
  ./v4gd3dbg $D/planted/$T.txt 14 search 1 -1 1 0 0 1 > $T.dbg.out 2> $T.dbg.err
  a=$(grep -o "nodes [0-9]*" $T.dbg.out); b=$(grep -o "nodes [0-9]*" $D/planted/$T.nosplit)
  s1=$(grep SOLUTION $T.dbg.out | sort | md5sum | cut -c1-8); s2=$(grep SOLUTION $D/planted/$T.nosplit | sort | md5sum | cut -c1-8)
  echo "$T dbg: $a vs orig: $b; sols $s1 vs $s2; $(tail -n 1 $T.dbg.err)"
done
for I in 29_0 11_6 5_0 19_0; do
  ./v4gd3dbg $KLEIN/gd_runs/inst/v4_$I.txt 14 search 1 5 16 3 1500 1 > real_$I.dbg.out 2> real_$I.dbg.err
  echo "real $I part3 nodelimit 1500: $(grep DONE real_$I.dbg.out) ; $(grep DBG real_$I.dbg.err | tail -n 1)"
done
