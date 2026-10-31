n=0; bad=0
for p in $(pgrep -f csp5p); do
  [ -r /proc/$p/environ ] || continue
  exe=$(readlink /proc/$p/exe 2>/dev/null)
  case "$exe" in *csp5p*) ;; *) continue;; esac
  n=$((n+1))
  if tr '\0' '\n' < /proc/$p/environ | grep -qE '^(STOP16|PLANT)='; then bad=$((bad+1)); echo "FLAG pid $p: $(tr '\0' '\n' < /proc/$p/environ | grep -E '^(STOP16|PLANT)=')"; fi
done
echo "$(hostname): csp5p processes checked $n, with STOP16/PLANT $bad"
p=$(pgrep -f csp5p | head -1); echo "sample exe $(readlink /proc/$p/exe) sha $(sha256sum $(readlink /proc/$p/exe) | cut -c1-16)"; tr '\0' ' ' < /proc/$p/cmdline; echo
