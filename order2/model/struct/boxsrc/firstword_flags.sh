#!/bin/bash
# firstword_flags.sh CI N SEED : (box) N random low words of code CI as forced first flag vector + MAXL continuation
# (flagbeam4 beam 1000) -> <HOME>/struct/fw/f{CI}_{word}.flag ; writes scan jobs <HOME>/struct/fw/jobs_{CI}.txt
ci=$1; n=$2; seed=$3; B=<HOME>/struct; export TMPDIR=$B/tmp; mkdir -p $B/fw
awk '{print $1}' $B/inst/data/low_$ci.txt | <HOME>/venv/bin/python -I -c "
import sys, random; w = [l.strip() for l in sys.stdin if l.strip()]; random.seed($seed); print('\n'.join(random.sample(w, min($n, len(w)))))" > $B/fw/words_$ci.txt
cat $B/fw/words_$ci.txt | xargs -P ${FWP:-70} -I{} sh -c 'f='"$B"'/fw/f'"$ci"'_{}.flag; [ -s $f ] || { MAXL=1 nice -n 10 '"$B"'/src/flagbeam4 '"$B"'/inst/data/gen_'"$ci"'.txt '"$B"'/inst/data/low_'"$ci"'.txt 1000 {} 2> /dev/null | grep "^FLAG" > $f.tmp && mv $f.tmp $f; }'
awk -v ci=$ci -v B=$B '{print ci, "fw"ci"_"$1, B"/fw/f"ci"_"$1".flag"}' $B/fw/words_$ci.txt > $B/fw/jobs_$ci.txt
echo "FW DONE $ci $(wc -l < $B/fw/jobs_$ci.txt)"
