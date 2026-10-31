#!/bin/bash
# check_box.sh: determinism check of this box's engine15 build: the 40 random valid X of validx40.txt through the
# queue mode must give J lines identical to join40.txt (computed on the main VM with the validated join engine).
set -e
cd "$(dirname "$0")"
export TMPDIR=$PWD/tmp
rm -rf tmp/qcheck; mkdir -p tmp/qcheck/queue tmp/qcheck/running tmp/qcheck/done tmp/qcheck/out
split -l 10 -d -a 3 validx40.txt tmp/qcheck/queue/a
( ulimit -v 2097152; nice -n 10 ./engine15 sep_A2.eng joinq tmp/qcheck 36 70 104 0 > /dev/null 2> tmp/qcheck/w0.err )
for f in tmp/qcheck/out/*.out; do grep '^J ' $f; done | sort > tmp/qcheck/j.txt
grep '^J ' join40.txt | sort > tmp/qcheck/ref.txt
if cmp -s tmp/qcheck/j.txt tmp/qcheck/ref.txt; then echo "CHECK_BOX OK: $(wc -l < tmp/qcheck/j.txt) J lines identical"; else echo "CHECK_BOX FAILED"; exit 1; fi
