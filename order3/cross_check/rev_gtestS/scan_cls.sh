#!/bin/bash
# one pass over the local cls24 copy: sha256 of uncompressed text, format check, aut>3.5 extraction, aut histogram
export TMPDIR=${TMPDIR:-.}
D=$(cd "$(dirname "$0")" && pwd)
zcat ${CLS:-$D/../../classification/class_list/cls24.txt.gz} | tee >(sha256sum > $D/scan_sha256.txt) | \
 awk -v D=$D 'BEGIN{bad=0}
 { if (length($1)!=192 || $1 !~ /^[0-9a-f]+$/ || NF!=5 || length($0)>8000) { bad++; if (bad<=20) print NR-1": "substr($0,1,300) > (D"/scan_bad.txt") }
   a=$2+0; h[a]++; if (a>3.5) print $0 > (D"/scan_aut4.txt") }
 END{ print "lines", NR, "bad", bad > (D"/scan_summary.txt"); for (k in h) print "aut", k, h[k] >> (D"/scan_summary.txt") }'
echo done >> $D/scan_summary.txt
