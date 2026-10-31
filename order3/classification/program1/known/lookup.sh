#!/bin/bash
# lookup.sh OUT: OUT = kc/fam output lines "name key aut a8 sc d ..."; prints per name: list id, list fields, comparison.
# Uses grep -F over cls24.txt (one pass; gunzip ../../class_list/cls24.txt.gz first, or set CLS).
D=$(cd "$(dirname "$0")" && pwd)
export TMPDIR=${TMPDIR:-$D} LC_ALL=C
OUT=$1; CLS=${CLS:-$D/../../class_list/cls24.txt}
K=$TMPDIR/lk_keys.$$; M=$TMPDIR/lk_match.$$
awk '$2 != "ERROR" {print $2}' $OUT | sort -u > $K
nice -n 10 grep -n -F -f $K $CLS > $M
awk -v M=$M 'BEGIN { while ((getline l < M) > 0) { split(l, p, ":"); split(p[2], f, " "); id[f[1]] = p[1] - 1; aut[f[1]] = f[2]; a8[f[1]] = f[3]; sc[f[1]] = f[4] } }
  $2 == "ERROR" { print $1, "ERROR", $3; nerr++; next }
  { k = $2; if (!(k in id)) { print $1, "NOT_FOUND aut=" $3, "A8=" $4, "sc=" $5; nmiss++; next }
    ok = (aut[k] == $3 && a8[k] == $4 && sc[k] == $5) ? "match" : "FIELD_MISMATCH";
    if (ok != "match") nbad++; else nok++;
    printf "%s id=%d list(aut=%s A8=%s sc=%s) computed(aut=%s A8=%s sc=%s) %s\n", $1, id[k], aut[k], a8[k], sc[k], $3, $4, $5, ok }
  END { printf "SUMMARY found+match %d, field mismatch %d, not found %d, errors %d\n", nok, nbad, nmiss, nerr }' $OUT
rm -f $K $M
