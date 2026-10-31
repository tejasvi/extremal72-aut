#!/usr/bin/env bash
# Checks the must-fail controls of this project, and checks the checker itself on its plants.
#
# A control states something false that a wrong definition or a missing hypothesis would make true, so it must not
# build. For each entry of controls_expected.txt the script runs `lake build <module>` and requires that the build
# fails with exactly one error in the module's own file, at the given line and column, with exactly the given
# message. A plant (plants_expected.txt) is a deliberately wrong case: a module that builds, one that fails for
# another reason, twice or in an earlier declaration, or a control checked against a wrong position or message.
# Every plant must be rejected.
#
# Run it from the directory that holds lakefile.lean, after building the libraries (see README.md):
#   ./check_controls.sh             controls and plants
#   ./check_controls.sh controls    controls only
#   ./check_controls.sh plants      plants only
# LAKE names the lake command (default: lake). The exit status is 0 if every control passes and every plant is
# rejected.
set -u
LAKE="${LAKE:-lake}"
HERE=$(cd "$(dirname "$0")" && pwd)
[ -f lakefile.lean ] || { echo "check_controls.sh: run it from the directory that holds lakefile.lean"; exit 2; }
MODE="${1:-all}"
case "$MODE" in all|controls|plants) ;; *) echo "usage: check_controls.sh [controls|plants]"; exit 2 ;; esac

# verdict <expected file> <module> <line:col> <build exit status>, with the build output on standard input
verdict() {
  awk -v mod="$2" -v want="$3" -v rc="$4" -v f="$(echo "$2" | tr . /).lean" '
    FNR == NR {
      if (substr($0, 1, 3) == "== ") { split($0, h, " "); inb = (h[2] == mod && h[3] == want); if (inb) seen++; next }
      if (inb) ex[++ne] = $0
      next
    }
    index($0, "error: ") == 1 {
      rest = substr($0, 8); i = index(rest, f ":")
      if (i > 0 && (i == 1 || substr(rest, i - 1, 1) == "/")) {
        n++
        if (n == 1) {
          p = substr(rest, i + length(f) + 1); split(p, q, ":"); pos = q[1] ":" q[2]
          m1 = substr(p, length(q[1]) + length(q[2]) + 3); sub(/^ /, "", m1); nm = 1; got[1] = m1; inm = 1
        } else inm = 0
        next
      }
      inm = 0; next
    }
    inm {
      if ($0 ~ /^(error|warning|info|trace): / || index($0, "Some required targets logged failures:") == 1 || $0 ~ /^(✖|⚠|✔|ℹ) /) { inm = 0; next }
      got[++nm] = $0
    }
    END {
      while (ne > 0 && ex[ne] == "") ne--
      while (nm > 0 && got[nm] == "") nm--
      same = (seen == 1 && n >= 1 && ne == nm)
      for (j = 1; same && j <= ne; j++) if (ex[j] != got[j]) same = 0
      if (rc != 0 && n == 1 && pos == want && same) print "PASS"
      else if (rc == 0) print "FAIL (the module builds)"
      else if (n != 1) printf "FAIL (%d errors in the module)\n", n
      else if (pos != want) printf "FAIL (error at %s, expected at %s)\n", pos, want
      else print "FAIL (the message differs)"
    }' "$1" -
}

# run <expected file> <control|plant>: prints one line per entry and a summary; returns 0 if all are as required
run() {
  local file="$1" kind="$2" total=0 good=0 mod pos out rc v
  while read -r mod pos; do
    total=$((total + 1))
    out=$("$LAKE" build "$mod" < /dev/null 2>&1); rc=$?
    v=$(printf '%s\n' "$out" | verdict "$file" "$mod" "$pos" "$rc")
    if [ "$kind" = control ]; then
      [ "$v" = PASS ] && good=$((good + 1))
      echo "control $mod: $v"
    elif [ "$v" = PASS ]; then
      echo "plant $mod: NOT REJECTED"
    else
      good=$((good + 1)); echo "plant $mod: rejected ${v#FAIL }"
    fi
  done < <(awk 'substr($0, 1, 3) == "== " {print $2, $3}' "$file")
  if [ "$kind" = control ]; then echo "controls: $good of $total pass"; else echo "plants: $good of $total rejected"; fi
  [ "$total" -gt 0 ] && [ "$good" -eq "$total" ]
}

status=0
if [ "$MODE" != plants ]; then run "$HERE/controls_expected.txt" control || status=1; fi
if [ "$MODE" != controls ]; then run "$HERE/plants_expected.txt" plant || status=1; fi
exit $status
