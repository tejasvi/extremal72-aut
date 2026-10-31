#!/bin/bash
# csp5p production driver (resumable work queue).  usage: run_list.sh WORKDIR LISTFILE[.gz|.xz] NWORKERS [CHUNK]
#   NWORKERS = per-box process cap.  WORKDIR gets: list.txt, chunks/, out/<chunk>.out, done/<chunk> marks,
#   locks/ (claims), tmp/ (TMPDIR), run.pid, progress.log.  Re-running the same command resumes: chunks with a done/
#   mark are skipped, half-finished chunks are redone from scratch.  Refuses to start if a previous driver for
#   WORKDIR is still alive.  Binary: $HERE/csp5p_static_v3 if present, else $HERE/csp5p; blocks: $HERE/octdod.txt.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
W=$1; LIST=$(readlink -f "$2"); NW=$3; CH=${4:-200}
BIN=$HERE/csp5p_static_v3; [ -x "$BIN" ] || BIN=$HERE/csp5p
[ -x "$BIN" ] || { echo "no csp5p binary in $HERE"; exit 1; }
mkdir -p "$W"/chunks "$W"/out "$W"/locks "$W"/done "$W"/tmp
export TMPDIR="$W/tmp"
cd "$W"
if [ -f run.pid ] && kill -0 "$(cat run.pid)" 2>/dev/null; then echo "driver already running (pid $(cat run.pid))"; exit 1; fi
echo $$ > run.pid
if [ ! -f list.txt ]; then
  case "$LIST" in
    *.gz) gzip -dc "$LIST" > list.txt.part && mv list.txt.part list.txt ;;
    *.xz) xz -dc "$LIST" > list.txt.part && mv list.txt.part list.txt ;;
    *)    cp "$LIST" list.txt.part && mv list.txt.part list.txt ;;
  esac
fi
if [ ! -f chunks/.split_done ]; then
  split -l "$CH" -d -a 7 list.txt chunks/c_ && touch chunks/.split_done
fi
rm -rf locks/*        # claims of an interrupted run are released; done/ marks are kept
echo "$(date -u) start: $(ls chunks | grep -c '^c_') chunks, $(ls done | wc -l) done, NW=$NW, BIN=$BIN" >> progress.log
worker() {
  for f in chunks/c_*; do
    b=${f#chunks/}
    [ -e "done/$b" ] && continue
    mkdir "locks/$b" 2>/dev/null || continue
    nice -n 10 "$BIN" 24 E "$f" "$HERE/octdod.txt" > "out/$b.out" 2> "out/$b.err" && touch "done/$b"
  done
}
for i in $(seq 1 "$NW"); do worker & done
wait
echo "$(date -u) end: $(ls done | wc -l) chunks done" >> progress.log
echo "ALL CHUNKS PROCESSED $(date -u)" > ALLDONE
rm -f run.pid
