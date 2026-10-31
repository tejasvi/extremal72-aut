"""patch_rc14.py SRC DST : rc14 = rc13 with the direct-table cap raised from 16 KB to 1 MB (more lanes read one table row
instead of translating a coset bitmap).  Same decisions and output.  Exact anchors, each must occur once."""
import sys
src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()
def rep(old, new):
    global s
    n = s.count(old)
    if n != 1: sys.exit(f"anchor found {n} times: {old[:80]!r}")
    s = s.replace(old, new)
rep("#define DCAP 16384           // direct table if 2^m * max(8, bitmap bytes) <= DCAP",
    "#define DCAP 1048576         // direct table if 2^m * max(8, bitmap bytes) <= DCAP (rc14: 1 MB, was 16 KB)")
open(dst, 'w').write(s)
print(f"patched {src} -> {dst}")
