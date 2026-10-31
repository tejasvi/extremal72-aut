"""Basic binary-code helpers (vectors are Python ints, bit i = coordinate i)."""
import itertools

CODES36 = "<HOME>/c72/c2/codes36.txt"


def read_code36(k, path=CODES36):
    """Code k (0-based): lines 19k+1 .. 19k+18 (1-based) of the file, 18 rows of 36 bits."""
    with open(path) as f:
        lines = f.read().split("\n")
    rows = lines[19 * k: 19 * k + 18]
    assert len(rows) == 18 and all(len(r) == 36 and set(r) <= {"0", "1"} for r in rows), rows
    if 19 * k + 18 < len(lines):
        assert lines[19 * k + 18].strip() == ""
    return [sum(1 << i for i, c in enumerate(r) if c == "1") for r in rows]


def wt(v):
    return bin(v).count("1")


def rref(vecs, n):
    """Row-reduce a list of int vectors; returns list of independent rows (pivot = lowest set bit), reduced."""
    rows = []
    for v in vecs:
        for r in rows:
            if v >> (r & -r).bit_length() - 1 & 1:
                v ^= r
        if v:
            p = v & -v
            rows = [r ^ v if r & p else r for r in rows]
            rows.append(v)
    return rows


def rank(vecs, n):
    return len(rref(vecs, n))


def span(basis):
    """All 2^k codewords of span(basis), Gray-code order; returns list (index i = combination of bits of i)."""
    k = len(basis)
    words = [0] * (1 << k)
    for i in range(1, 1 << k):
        low = (i & -i).bit_length() - 1
        words[i] = words[i ^ (1 << low)] ^ basis[low]
    return words


def dot(a, b):
    return wt(a & b) & 1


def weight_distribution(words, n):
    wd = [0] * (n + 1)
    for w in words:
        wd[wt(w)] += 1
    return wd


def dual_basis(basis, n):
    """Basis of the dual code of span(basis) in F2^n."""
    rows = rref(basis, n)
    piv = [(r & -r).bit_length() - 1 for r in rows]
    free = [j for j in range(n) if j not in piv]
    out = []
    for j in free:
        v = 1 << j
        for r, p in zip(rows, piv):
            if r >> j & 1:
                v |= 1 << p
        out.append(v)
    for v in out:
        assert all(dot(v, r) == 0 for r in rows)
    return out


def vec_to_str(v, n):
    return "".join("1" if v >> i & 1 else "0" for i in range(n))
