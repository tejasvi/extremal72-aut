"""Split the unfinished part of list_f between two boxes.
usage: split_listf.py NUM DEN OUT_A OUT_B DONE_GLOB...
done set = reps with a complete W line in any file of DONE_GLOB (strict per-file parsing, as close_ledger22.py).
Remaining = split/list_f.txt minus done, in list order; rep i of the remaining list goes to OUT_A if i % DEN < NUM,
else OUT_B (interleaved, so both lists have the same mix of cheap early and expensive late reps)."""
import glob, sys
D = "<HOME>/c72_indep/y22/"
num, den, outa, outb = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
done = set()
for pat in sys.argv[5:]:
    for fn in sorted(glob.glob(pat)):
        with open(fn, "rb") as fh:
            for raw in fh:
                if raw.startswith(b"W ") and raw.endswith(b"\n"):
                    t = raw.decode(errors="replace").split()
                    if len(t) == 7:
                        try:
                            [int(u) for u in t[2:]]
                            done.add(t[1])
                        except ValueError:
                            pass
lines = [l for l in open(D + "split/list_f.txt") if l.strip()]
rem = [l for l in lines if l.split()[1] not in done]
A = [l for i, l in enumerate(rem) if i % den < num]
B = [l for i, l in enumerate(rem) if i % den >= num]
open(outa, "w").write("".join(A))
open(outb, "w").write("".join(B))
print("list_f %d, done %d (of which in list_f %d), remaining %d -> A %d, B %d"
      % (len(lines), len(done), len(lines) - len(rem), len(rem), len(A), len(B)))
assert len(A) + len(B) == len(rem) and not (set(A) & set(B))
