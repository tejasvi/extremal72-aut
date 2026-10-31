#!/bin/bash
# Re-run xcheck_cmp.py (the seeded selection of cross-check parts, the reruns with the reference program, their
# integrity and setup, and the split cross-checks through xsplit_cmp.py) on package runs of this archive, and check that
# every line it prints also appears in the run's recorded summary (runs/RUN/summary/RUN_SUMMARY.txt).
# Usage: run_xcheck_cmp.sh [-o OUTDIR] RUN [RUN ...]   (package runs; the eight runs made outside the package fleet are
# covered by their coverage reports). Part logs are unpacked into OUTDIR/RUN/, which must not exist yet; nothing inside
# the archive tree is written.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)          # order2/model/explore
O2=$(cd "$HERE/../.." && pwd)                 # order2
OUT=./xcheck_out
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
  local r=$1 W=$OUT/$1 f
  valid "$r" || return
  if [ ! -d "$O2/packages/$r" ]; then echo "$r: not a package run, see its coverage report"; return; fi
  mkdir -p "$W"
  for f in "$O2/runs/$r"/*; do case $f in *.tar.gz) tar -xzf "$f" -C "$W" ;; *) ln -s "$f" "$W/$(basename "$f")" ;; esac; done
  local np; np=$(awk '$1=="NPART"{print $2}' "$O2/packages/$r/PLAN.txt")
  XC_RESULTS="$W" C2E_TEST_RESULTS="$W" $PY "$HERE/xcheck_cmp.py" "$r" "$np" "$O2/packages/$r" > "$OUT/xcheck_$r.txt" 2>&1
  local n miss sp
  grep -E '^xcheck (selection|SHA256SUMS|setup|[0-9]+/[0-9]+)' "$OUT/xcheck_$r.txt" > "$OUT/xcheck_$r.core"
  n=$(grep -c . "$OUT/xcheck_$r.core")
  # records whose sha256 another record cites keep the working-directory labels (c2 + name); the checker prints the name
  nl() { sed -E 's/(^|[^A-Za-z0-9])c2([a-z]+)/\1\2/g' "$1"; }
  miss=$(grep -v -x -F -f <(nl "$O2/runs/$r/summary/RUN_SUMMARY.txt") <(nl "$OUT/xcheck_$r.core") | grep -c .)
  sp=$(grep -c -E '^  p[0-9]+: IDENTICAL' "$OUT/xcheck_$r.txt")
  if [ "$sp" -gt 0 ]; then
    local sd; sd=$(grep -c -E '^  p[0-9]+: DIFFERENT' "$OUT/xcheck_$r.txt")
    sp=" | split cross-checks: $sp parts IDENTICAL, $sd DIFFERENT"
  else sp=""; fi
  if [ "$n" -gt 0 ] && [ "$miss" -eq 0 ]; then echo "$r: $(grep -E '^xcheck [0-9]+/[0-9]+' "$OUT/xcheck_$r.txt" | tail -1) | all $n summary lines equal to the recorded ones$sp"
  else echo "$r: $miss of $n summary lines not found in the recorded summary, see $OUT/xcheck_$r.txt$sp"; fi
}
if [ "${1:-}" = all ]; then set -- $(ls "$O2/packages"); fi
for r in "$@"; do
  if [ -f "$O2/runs/$r/PLACEHOLDER.txt" ]; then echo "$r: placeholder, skipped"; continue; fi
  one "$r"
done
