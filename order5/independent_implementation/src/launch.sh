#!/bin/bash
# launch.sh LOGFILE CMD... : run CMD detached (new session, all fds redirected)
log=$1; shift
setsid nohup "$@" > "$log" 2>&1 < /dev/null &
disown
exit 0
