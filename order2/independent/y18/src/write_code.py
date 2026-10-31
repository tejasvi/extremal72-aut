"""Write generator rows of C_B for the mincheck program."""
import sys
sys.path.insert(0, "<HOME>/c72_indep/y18/src")
def write_rows(rows, N, path):
    with open(path, "w") as f:
        f.write("%d %d\n" % (N, len(rows)))
        for r in rows:
            f.write("%016x %016x\n" % (r >> 64, r & ((1 << 64) - 1)))
