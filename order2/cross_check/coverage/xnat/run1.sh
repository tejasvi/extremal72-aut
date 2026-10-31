#!/bin/bash
# Re-run one whole production part with the audit's portable lwe8 build (src 3d58cf5d, own gcc build abe524dc) and
# compare with the production log: DONE line without the time field, all LEVEL lines, the closing line.
# usage: run1.sh CODE PARTSDIR PART CLASS      (single core, nice 10, timeout 540 s; appends to results.txt)
set -u
export TMPDIR=<HOME>/c72/audit/c2audit/tmp
X=<HOME>/c72/audit/c2audit/c3/xnat; cd $X || exit 1
c=$1; d=$2; q=$3; cls=$4
P=<HOME>/c72/explore/runs2/$c
SPL=$(awk '$1=="SPLIT_LEVEL"{print $2}' $P/PLAN.txt); NPART=$(awk '$1=="NPART"{print $2}' $P/PLAN.txt)
out=$X/out/${c}_p$q.log; mkdir -p $X/out
s=$(date +%s)
env -u SYMFILE -u LTSFILE -u PROBES -u ALARM LTSHFILE=$P/sym.ltsh timeout 540 nice -n 10 $X/../lwe8_ref $P/inst.txt $SPL $NPART $q > $out 2>&1
rc=$?; el=$(( $(date +%s) - s ))
norm() { grep -E '^(DONE|LEVEL|SYMPRUNE)' "$1" | sed -E 's/ time [0-9]+s//'; }
if [ $rc -ne 0 ] || grep -q STOPPED $out; then v="INCOMPLETE rc $rc"
elif diff <(norm $out) <(norm $P/$d/p$q.log) > /dev/null; then v=IDENTICAL
else v=DIFFERENT; fi
pt=$(grep -o 'time [0-9]*s' $P/$d/p$q.log)
echo "$(date -u +%FT%TZ) $c p$q/$NPART split $SPL class $cls prod_$pt audit_time ${el}s $v $(sha256sum < $out | cut -c1-16)" | tee -a $X/results.txt
