#!/bin/bash
# scoreboard.sh : summarise all sample-part groups in logs/scanparts (group = name before _p<part>)
D=<HOME>/c72/c2opt/struct; cd $D
for g in $(ls logs/scanparts/*_p*.log 2>/dev/null | sed 's#.*/##; s/_p[0-9]*\.log$//' | sort -u); do
  spl=$(echo $g | sed -n 's/.*_s\([0-9]\).*/\1/p'); np=200000
  case $g in *n20k*) np=20000;; *n400k*) np=400000;; esac
  n=$(ls logs/scanparts/${g}_p*.time 2>/dev/null | xargs -r grep -l user | wc -l)
  [ "$n" = 0 ] && continue
  r=$(<HOME>/c72/venv/bin/python -I src/partsum.py $spl $np $(for t in $(ls logs/scanparts/${g}_p*.time | xargs grep -l user); do echo ${t%.time}.log; done) | tail -1)
  echo "$g [$n parts]: $r"
done
