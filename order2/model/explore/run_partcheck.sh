#!/bin/bash
# Re-run partcheck.py (structure of every part log, identical prefix in all parts, LBPRUNE lines of LTSB runs) on runs of
# this archive and compare its summary line with the one recorded at the time of the run.
# Usage: run_partcheck.sh [-o OUTDIR] RUN [RUN ...]     (RUN = y0-lb, y1b, ..., y40, or "all"; Y39 is not covered)
# Part logs are unpacked into OUTDIR/RUN/, which must not exist yet; nothing inside the archive tree is written.
# Default OUTDIR: ./partcheck_out.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)          # order2/model/explore
O2=$(cd "$HERE/../.." && pwd)                 # order2
OUT=./partcheck_out
if [ "${1:-}" = "-o" ]; then OUT=$2; shift 2; fi
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
PY=${PYTHON:-python3}
export PYTHONDONTWRITEBYTECODE=1          # no bytecode caches inside the archive tree
valid() {  # RUN must name a directory under order2/runs/; OUTDIR/RUN must not exist yet (nothing is deleted)
  case $1 in ''|*/*|.*) echo "$1: no such run in this archive"; return 1 ;; esac
  [ -d "$O2/runs/$1" ] || { echo "$1: no such run in this archive"; return 1; }
  [ -e "$OUT/$1" ] && { echo "$1: $OUT/$1 exists; use a new OUTDIR"; return 1; }
  return 0
}
one() {
  local r=$1 W=$OUT/$1 pk main=parts rec
  case $r in
    y39) echo "y39: not covered (its run predates partcheck; see the coverage report)"; return ;;
    y1b|y29) main=parts_all ;; y4|y5b) main=parts_hostC ;; y22|y23) main=parts_hostB ;;
  esac
  valid "$r" || return
  pk="$O2/packages/$r"; [ -d "$pk" ] || pk="$O2/runs/$r"
  mkdir -p "$W"
  tar -xzf "$O2/runs/$r/$main.tar.gz" -C "$W"
  local np spl
  np=$(awk '$1=="NPART"{print $2}' "$pk/PLAN.txt"); spl=$(awk '$1=="SPLIT_LEVEL"{print $2}' "$pk/PLAN.txt")
  $PY "$HERE/partcheck.py" "$pk" "$W/$main" "$np" "$spl" > "$OUT/partcheck_$r.txt" 2>&1
  local new; new=$(grep -m1 '^partcheck:' "$OUT/partcheck_$r.txt")
  rec=$(grep -h -m1 '^partcheck:' "$O2/runs/$r/PARTCHECK.txt" "$O2/runs/$r/summary/RUN_SUMMARY.txt" 2>/dev/null | head -1)
  local verdict; verdict=$(grep -E '^PARTCHECK' "$OUT/partcheck_$r.txt" | tail -1)
  if [ -n "$rec" ] && [ "$new" = "$rec" ]; then echo "$r: $verdict | summary line equal to the recorded one"
  else echo "$r: $verdict | summary line differs from the record: [$new] vs [$rec]"; fi
}
if [ "${1:-}" = all ]; then set -- $(ls "$O2/runs"); fi
for r in "$@"; do
  if [ -f "$O2/runs/$r/PLACEHOLDER.txt" ]; then echo "$r: placeholder, skipped"; continue; fi
  one "$r"
done
