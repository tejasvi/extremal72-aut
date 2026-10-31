#!/bin/bash
# prefix.sh CODEDIR SPL : enumerate levels <= SPL only (no part selected) and print per-level nodes/lhprune + user time
D=$1; S=$2
LTSHFILE=$D/sym.ltsh nice -n 10 /usr/bin/time -f "user %U" <HOME>/c72/c2opt/struct/runs/frozen3/lwe10 $D/inst.txt $S 1000000000 999999999 2>&1 | grep -E "^LEVEL [0-$S] |^user" | awk -v d=$D -v s=$S '{if ($1=="LEVEL") printf "L%s %s/%s ", $2, $8, $16; else printf "%s\n", $0}' | sed "s#^#$(basename $D) spl$S: #"
