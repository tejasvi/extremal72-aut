#!/bin/bash
# run all C2xC2 instances: 16 parts each (split at depth 5), skip finished tasks; P parallel at nice 10
cd "$(dirname "$0")"
mkdir -p out
P=${1:-280}
ls inst/v4_*.txt | sed 's#inst/v4_\(.*\)\.txt#\1#' | grep -v '^0_0$' | while read inst; do
  for p in $(seq 0 15); do echo "$inst $p"; done
done | shuf --random-source=<(yes) > tasks.txt
cat tasks.txt | xargs -P $P -L 1 bash -c 'f=out/v4_$0_$1.out; if grep -q "^DONE result=COMPLETE" $f 2>/dev/null; then exit 0; fi; nice -n 10 ./v4gd3 inst/v4_$0.txt 14 search 1 5 16 $1 0 1 > $f 2> out/v4_$0_$1.err'
echo ALLDONE > out/ALLDONE
