#!/bin/bash
# usage: verify_sat.sh "E code line (layout A or B)" "golay basis g1,...,g12 (hex)" [NPARTS]
# Builds C = F + E_bin (length 72) and computes its full weight distribution with NPARTS parallel slices.
D=$(cd "$(dirname "$0")" && pwd); NP=${3:-16}
export TMPDIR=${TMPDIR:-$D/tmp}; mkdir -p "$TMPDIR"
OUT=$D/run_$$; mkdir -p $OUT
for p in $(seq 0 $((NP-1))); do nice -n 10 $D/verify_c 24 "$1" "$2" $p $NP > $OUT/p$p.txt & done
wait
python3 -I - "$OUT" << 'PY'
import sys, glob, re, collections
h = collections.Counter(); head = None
for f in glob.glob(sys.argv[1] + '/p*.txt'):
    lines = open(f).read().splitlines(); head = lines[0]
    for t in re.findall(r'(\d+):(\d+)', lines[1].split('weights:')[1]): h[int(t[0])] += int(t[1])
print(head)
nz = sorted(w for w in h if w > 0)
print("TOTAL words", sum(h.values()), "min nonzero weight", nz[0] if nz else None)
print("weights:", " ".join("%d:%d" % (w, h[w]) for w in sorted(h)))
ext = {16: 249849, 20: 18106704, 24: 462962955}
print("EXTREMAL [72,36,16]" if nz and nz[0] == 16 and all(h[w] == c for w, c in ext.items()) else "not extremal")
PY
