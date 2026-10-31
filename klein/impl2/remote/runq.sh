#!/bin/bash
# usage: runq.sh <cmdfile> <parallel>   (runs in the impl2 directory; every command line is self-contained)
cd "$(dirname "$0")/.."
mkdir -p out
xargs -P "$2" -I{} sh -c '{}' < "$1"
echo DONE > "$1.done"
