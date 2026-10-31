#!/bin/bash
# start share_local3 (14 workers) once the share_local pool has exited
F=$(cd "$(dirname "$0")" && pwd)
while [ -f $F/share_local/run.pid ] && kill -0 "$(cat $F/share_local/run.pid)" 2>/dev/null; do sleep 20; done
export TMPDIR=$F/share_local3/tmp; mkdir -p $TMPDIR
cd $F/share_local3 && ./rg_run.sh $F/share_local3 14 > pool.log 2>&1
