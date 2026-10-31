#!/bin/bash
# mkfixed.sh CI : flag = [a G-fixed low word (weight 8 preferred)] + MAXL continuation (flagbeam4 beam 1000)
# -> inst/starts/fx{CI}.flag ; prints a scan-job line
ci=$1; D=<HOME>/c72/c2opt/struct; export TMPDIR=$D/tmp
W=$(grep "^$ci " $D/logs/fixedwords.txt | sed 's/^[0-9]* //' | tr -d '[]()' | tr ',' ' ' | awk '{best=""; for(i=1;i<=NF;i+=2){if(best==""||$i<bw){bw=$i; best=$(i+1)}} print best}')
[ -z "$W" ] && exit 0
f=$D/inst/starts/fx$ci.flag
[ -s $f ] || MAXL=1 nice -n 10 $D/src/flagbeam4 $D/inst/data/gen_$ci.txt $D/inst/data/low_$ci.txt 1000 "$W" 2> /dev/null | grep "FLAG\|PEAK" > $f
echo "$ci fx$ci $f 50000"
