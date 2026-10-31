#!/bin/bash
# Re-run the coverage checker cov_c2.py on runs of this archive and compare each new report with the shipped one.
# Usage: run_coverage.sh [-o OUTDIR] RUN [RUN ...]     (RUN = y0-lb, y1b, ..., y40, or "all")
# For each run the part logs (and second runs) are unpacked into OUTDIR/RUN/ (which must not exist yet) next to links
# to the run's records;
# nothing inside the archive tree is written. Default OUTDIR: ./coverage_out. Python 3 is taken from $PYTHON or PATH.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)          # order2/cross_check/coverage
O2=$(cd "$HERE/../.." && pwd)                 # order2
OUT=./coverage_out
if [ "${1:-}" = "-o" ]; then OUT=$2; shift 2; fi
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
PY=${PYTHON:-python3}
export PYTHONDONTWRITEBYTECODE=1          # no bytecode caches inside the archive tree
# executables allowed in main runs (sha256, as in engines/BINARIES.sha256): rc7, lwe11b, rc9, lwe11b3, rc11, lwe11b5,
# rc13, lwe11b7, rc14; the rc14g builds are allowed only for their own package
ENG=645a9f5c7cc831817e131059846714c561c0c9484728632744667439061255b0,2fdae1bb9bc924e2dc54be91482d64f5ae89e3fa1406bb1b0aa69a5b1757b941,dfbad27a7e9d69668eb8530226a6afa16fcc6925236b7c77529e18b7e4514424,3eddc9a884ef9fae1ad953e96a4292098524e6304d7c2c99908dd00f2ae1e3f3,cb04bfa878225611d671c158df0d6bdf36bca405e2a19bf87ba9826ea5259455,268d592dbec3e4da07672ade5701529543425fb3cc21ffcba8e0916afbae3348,2cd44f916033e388a9f8cca85bf0487ba0389212b6700001339bb85c92aa4200,ab9f2df8c3823a3406ce045281e920221e7bc2294402c229f6ee44a636c39464,ed00eb07620323370f36385a52fc27241068438ea6d757ff5ed14918b4386664
declare -A RC14G=( [y40]=8d6b797215e4679146a2dc86c58370fee8cae3d53cb4ce7e62552a1a5d1929b8 [y12-lb2]=7eeb6552a26bf15c62847685c3f46a3dccd6c87824ae6d70ef44b3b837ea2c9a [y15-lb]=f670798e1f52e38856fa3e4cc5666f0a325fd2b8975bc69c9b54703bcd115359 )
valid() {  # RUN must name a directory under order2/runs/; OUTDIR/RUN must not exist yet (nothing is deleted)
  case $1 in ''|*/*|.*) echo "$1: no such run in this archive"; return 1 ;; esac
  [ -d "$O2/runs/$1" ] || { echo "$1: no such run in this archive"; return 1; }
  [ -e "$OUT/$1" ] && { echo "$1: $OUT/$1 exists; use a new OUTDIR"; return 1; }
  return 0
}
unpack() {  # unpack RUN: links to the records and the unpacked part logs in OUT/RUN (its base name is the run name)
  local r=$1 W=$OUT/$1 f t
  mkdir -p "$W"
  for f in "$O2/runs/$r"/*; do
    case $(basename "$f") in
      inputs) ;;                                   # Y39: the run's inputs, read through --inputs-root
      *.tar.gz) tar -xzf "$f" -C "$W" ;;
      *) ln -s "$f" "$W/$(basename "$f")" ;;
    esac
  done
}
compare() {  # compare RUN: new report against the shipped one; directory paths and the order of family labels may differ
  local r=$1
  if [ ! -f "$HERE/cov_$r.txt" ]; then echo "$r: no shipped report"; return; fi
  norm() { python3 -c 'import re,sys
for l in open(sys.argv[1]):
    l = re.sub(r"^package [^:]*:", "package <dir>:", l)
    l = re.sub(r"^(note: alt dir )\S*?/(parts_[^ :]*):", r"\1<dir>/\2:", l)
    l = re.sub(r"\(full checks per family/engine: ([^)]*)\)", lambda m: "(full checks per family/engine: " + ", ".join(sorted(m.group(1).split(", "))) + ")", l)
    l = re.sub(r"(combinations: )(.*)$", lambda m: m.group(1) + ", ".join(sorted(m.group(2).split(", "))), l)
    if l.startswith("note: input files edited for publication"): continue
    sys.stdout.write(l)' "$1"; }
  if diff <(norm "$HERE/cov_$r.txt") <(norm "$OUT/cov_$r.txt") > "$OUT/cov_$r.diff"; then
    echo "$r: $(grep -E '^VERDICT' "$OUT/cov_$r.txt") | report identical to the shipped one (directory paths excepted)"
  else
    echo "$r: $(grep -E '^VERDICT' "$OUT/cov_$r.txt") | report differs from the shipped one, see $OUT/cov_$r.diff"
  fi
}
one() {
  local r=$1 W=$OUT/$1 xc=() alt=()
  valid "$r" || return
  unpack "$r"
  case $r in
    y39) $PY "$HERE/cov_c2.py" --pkg "$W" --parts "$W" --npart 2000 --split 3 --inputs-root "$O2/runs/y39/inputs" \
           --inst "$O2/runs/y39/inputs/inst/y39_ginv.txt" --prefix "$HERE/prefix_y39.txt" --report "$OUT/cov_y39.txt" --allow-sym > /dev/null ;;
    y1b|y4|y5b|y8|y22|y23|y29)
      local main=parts
      case $r in
        y1b) main=parts_all; alt=(--alt "$W/parts_hostB" --alt "$W/parts_hostC" --alt "$W/parts_local") ;;
        y4) main=parts_hostC; alt=(--alt "$W/parts_local") ;;
        y5b) main=parts_hostC ;;
        y22|y23) main=parts_hostB ;;
        y29) main=parts_all; alt=(--alt "$W/parts_hostK/parts" --alt "$W/parts_hostL/parts") ;;
      esac
      [ -d "$W/xcheck" ] && xc=(--xcheck "$W/xcheck")
      $PY "$HERE/cov_c2.py" --pkg "$W" --parts "$W/$main" --inputs-base "$O2/model/struct" --prefix "$HERE/prefix_$r.txt" \
           --report "$OUT/cov_$r.txt" "${xc[@]}" "${alt[@]}" > /dev/null ;;
    *) $PY "$HERE/cov_c2.py" --pkg "$O2/packages/$r" --parts "$W/parts" --fleet "$W" --inputs-base "$O2/model/struct" \
           --engines "$ENG${RC14G[$r]:+,${RC14G[$r]}}" --prefix "$HERE/prefix_$r.txt" --report "$OUT/cov_$r.txt" > /dev/null ;;
  esac
  if grep -q '^PROBLEM: INPUTS.sha256 mismatch' "$OUT/cov_$r.txt"; then   # input files edited for publication
    local pk="$O2/packages/$r"; [ -d "$pk" ] || pk="$O2/runs/$r"
    $PY "$HERE/cov_redacted.py" "$OUT/cov_$r.txt" "$pk" "$O2/REDACTIONS.tsv" "$OUT/cov_$r.acc" > /dev/null && mv "$OUT/cov_$r.acc" "$OUT/cov_$r.txt"
  fi
  compare "$r"
}
if [ "${1:-}" = all ]; then set -- $(ls "$O2/runs"); fi
for r in "$@"; do
  if [ -f "$O2/runs/$r/PLACEHOLDER.txt" ]; then echo "$r: placeholder, skipped"; continue; fi
  one "$r"
done
