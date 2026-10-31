#!/bin/bash
# Reference queue: run bin/lwe8 on the seeded production parts (logs/ref/PARTS.txt), interleaved by code, NPROC at a time.
# Resumable: a part whose .log has a DONE line is skipped.  Usage: refqueue.sh NPROC [BIN TAG]
set -u
cd <HOME>/c72/c2opt/alg
export TMPDIR=<HOME>/c72/c2opt/alg/tmp
NPROC=$1; BIN=${2:-bin/lwe8}; TAG=${3:-lwe8}
python3 - "$TAG" > logs/ref/queue_$TAG.txt << 'PY'
import sys
rows = [l.split() for l in open('logs/ref/PARTS.txt') if not l.startswith('#')]
for i in range(20):
    for r in rows:
        print(r[0], r[1], r[2], r[3 + i])
PY
cat logs/ref/queue_$TAG.txt | xargs -P $NPROC -L 1 sh -c 'f=logs/ref/$0_p$3_'$TAG'; if [ -s $f.log ] && grep -q "^DONE" $f.log && ! grep -q STOPPED $f.log; then exit 0; fi; src/runpart.sh '$BIN' $0 $1 $2 $3 $f'
echo QUEUE_DONE
