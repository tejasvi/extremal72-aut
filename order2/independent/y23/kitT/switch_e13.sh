#!/bin/bash
# switch_e13.sh: stop this kit's engine12 workers (explicit PIDs; argv and cwd checked), keep their partial files in
# aborted_e12/, set ENGINE to engine13. Touches no other process.
cd "$(dirname "$0")"
D=$PWD
pids_of() {  # $1 = awk condition on the args; prints PIDs whose cwd is this kit dir
  ps -u $(id -u) -o pid=,args= | awk "$1 {print \$1}" | while read p; do
    [ "$(readlink /proc/$p/cwd 2>/dev/null)" = "$D" ] && echo $p
  done
}
WP=$(pids_of '$2=="/bin/bash" && $3=="./worker.sh"')
echo "workers: $(echo $WP | wc -w)"
[ -n "$WP" ] && kill $WP
sleep 2
left=$(pids_of '$2=="/bin/bash" && $3=="./worker.sh"')
[ -n "$left" ] && { echo "workers still alive: $left"; exit 1; }
EP=$(pids_of '$2=="./engine12" && $4=="joinstab"')
echo "engine12: $(echo $EP | wc -w)"
[ -n "$EP" ] && kill $EP
sleep 2
left=$(pids_of '$2=="./engine12"')
[ -n "$left" ] && { echo "engine12 still alive: $left"; exit 1; }
mkdir -p aborted_e12
mv running/* aborted_e12/ 2>/dev/null; mv out/*.tmp out/*.err aborted_e12/ 2>/dev/null
echo "done items kept: $(ls done | wc -l); queue: $(ls queue | wc -l); running: $(ls running | wc -l)"
echo engine13 > ENGINE
echo "ENGINE=$(cat ENGINE) $(date -u)"
