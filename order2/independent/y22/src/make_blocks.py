"""Write a separator spec with explicit block order: blocks = lists of weight-8 words inside given coordinate sets
(in the given order; a word goes to the first block whose set contains it)."""
import sys, ast
K = int(sys.argv[1]); DIR = sys.argv[2]; base = sys.argv[3]; out = sys.argv[4]
sys.path.insert(0, DIR + "/src")
from codes import *
spec = ast.literal_eval(open(base).read())
words = span(read_code36(K))
W8 = [v for v in words if wt(v) == 8]
sets = [int(s, 16) for s in sys.argv[5:]]
blocks, used = [], set()
for S in sets:
    b = [v for v in W8 if v & ~S == 0 and v not in used]
    used |= set(b)
    blocks.append(b)
spec["block_words"] = blocks
open(out, "w").write(repr(spec))
print("blocks sizes:", [len(b) for b in blocks])
