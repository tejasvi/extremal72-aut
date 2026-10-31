#!/bin/bash
# fw_total.sh CI : (box) for each word in fw/words_CI.txt (or 300 random low words): forced first word + flagbeam4
# total-nodes objective (beam 1000 and 3000); scan each.  Jobs run in parallel via xargs (P from env FWP, default 90).
ci=$1; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/fwt
[ -s $B/fw/words_$ci.txt ] || awk '{print $1}' $B/inst/data/low_$ci.txt | <HOME>/venv/bin/python -I -c "
import sys, random; w=[l.strip() for l in sys.stdin if l.strip()]; random.seed($ci*7+1); print('\n'.join(random.sample(w, min(300, len(w)))))" > $B/fw/words_$ci.txt
for b in 1000 3000; do awk -v b=$b '{print $1, b}' $B/fw/words_$ci.txt; done | xargs -P ${FWP:-90} -L 1 sh -c 'f='"$B"'/fwt/t'"$ci"'_$0_$1.flag; [ -s $f ] || XX=1 nice -n 10 '"$B"'/src/flagbeam4 '"$B"'/inst/data/gen_'"$ci"'.txt '"$B"'/inst/data/low_'"$ci"'.txt $1 $0 2> /dev/null | grep "^FLAG" > $f; '"$B"'/boxsrc/scan_box.sh '"$ci"' fwt_$0_$1 $f 50000'
echo "FWT DONE $ci"
