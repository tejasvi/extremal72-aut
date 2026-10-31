#!/bin/bash
# lawtest.sh BIN10 BIN9 CODEDIR SPL NPART PART LAWFILE OUT : rc10 LAWFILE checks on one part, sequentially (1 core).
# (a) no LAWFILE: LEVEL/DONE/SOL identical to rc9; count mode: LEVEL/DONE/SOL identical to rc9;
# (b) prune mode: LEVEL lines == count mode LAWOK LEVEL lines, pruned == violating, nsol == LAWOK nsol; prune + CHECK passes.
B10=$1; B9=$2; D=$3; SPL=$4; NP=$5; PT=$6; LAWF=$7; O=$8
export TMPDIR=<HOME>/c72/c2opt/alg/tmp
hsh() { grep -E '^LEVEL|^DONE|^SOL' $1 | sed 's/time [0-9]*s//' | sha256sum | cut -c1-16; }
r() { local tag=$1; shift; env LTSHFILE=$D/sym.ltsh "$@" nice -n 10 $BIN $D/inst.txt $SPL $NP $PT > $O.$tag.log 2> $O.$tag.err; }
BIN=$B9 r rc9; BIN=$B10 r none; BIN=$B10 r count LAWFILE=$LAWF LAWCOUNT=1; BIN=$B10 r prune LAWFILE=$LAWF; BIN=$B10 r chk LAWFILE=$LAWF LWE11CHECK=1
h9=$(hsh $O.rc9.log); hn=$(hsh $O.none.log); hc=$(hsh $O.count.log)
pl=$(grep '^LEVEL' $O.prune.log | sha256sum | cut -c1-16); cl=$(grep '^LAWOK LEVEL' $O.count.log | sed 's/^LAWOK //' | sha256sum | cut -c1-16)
pr=$(grep '^LAW ' $O.prune.log | awk '{print $NF}'); vi=$(grep '^LAW ' $O.count.log | awk '{print $NF}')
ns=$(grep '^DONE' $O.prune.log | awk '{print $4}'); nc=$(grep '^LAWOK SYMPRUNE' $O.count.log | awk '{print $NF}')
sp=$(grep '^SOL' $O.prune.log | sort | sha256sum | cut -c1-16); cp=$(grep -c '^SOL' $O.prune.log)
pc=$(grep '^LEVEL' $O.prune.log | sha256sum | cut -c1-16); kc=$(grep '^LEVEL' $O.chk.log | sha256sum | cut -c1-16)
echo "$(basename $O) law $(grep '^LAW ' $O.prune.log | cut -d' ' -f2-7) | none==rc9 $([ $h9 = $hn ] && echo Y || echo N) count==rc9 $([ $h9 = $hc ] && echo Y || echo N) prune==LAWOK $([ $pl = $cl ] && echo Y || echo N) pruned $pr violating $vi $([ "$pr" = "$vi" ] && echo Y || echo N) nsol $ns/$nc chk==prune $([ $pc = $kc ] && echo Y || echo N) [$(tail -2 $O.chk.err | tr '\n' ' ')]"
