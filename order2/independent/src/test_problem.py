import sys, random
sys.path.insert(0, "<HOME>/c72_indep/src")
from problem import *
from linalg import *
P = Problem(read_code36(39), 36, 16)
random.seed(1)
def random_form(P):
    N = P.FS.N
    v = random.getrandbits(N)
    # correct diag
    funcs = [f for f, c in P.diag]
    tg = [c ^ (bin(f & v).count("1") & 1) for f, c in P.diag]
    d = solve(funcs, tg)
    return P.vec_to_gram(v ^ d)
for _ in range(3):
    M = random_form(P)
    print("valid:", P.is_valid_form(M))
    rows = P.code_CB(M)
    # check self-orthogonality and doubly-evenness of generators
    ok = all(bin(a & b).count("1") % 2 == 0 for a in rows for b in rows) and all(bin(a).count("1") % 4 == 0 for a in rows)
    print("C_B self-orth & doubly-even generators:", ok, "rank", rank(rows, 72))
