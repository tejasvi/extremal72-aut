n=0; bad=0
for p in $(pgrep -x gtestS); do
  n=$((n+1))
  v=$(tr '\0' '\n' < /proc/$p/environ 2>/dev/null | grep -E '^(NOL1|ROOTEX|SYM|MAXSCAN|SAMPLE2|LOOKUPFP|DEBUGFP|PROG|STOP16|PLANT)=')
  if [ -n "$v" ]; then bad=$((bad+1)); [ $bad -le 3 ] && echo "FLAG pid $p: $v"; fi
done
echo "$(hostname): gtestS processes checked $n, with special env vars $bad"
