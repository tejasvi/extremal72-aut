#!/bin/bash
# start share_local4b (13 workers) once the share_local2 and share_local3 pools have exited
F=$(cd "$(dirname "$0")" && pwd)
alive() { [ -f $1/run.pid ] && kill -0 "$(cat $1/run.pid)" 2>/dev/null; }
while alive $F/share_local2 || alive $F/share_local3; do sleep 15; done
export TMPDIR=$F/share_local4b/tmp; mkdir -p $TMPDIR
cd $F/share_local4b && ./rg_run.sh $F/share_local4b 13 > pool.log 2>&1
