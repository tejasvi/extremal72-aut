"""Basic GF(2) linear algebra on Python ints (bit i = coordinate i)."""
import re

def popcount(x):
    return bin(x).count("1")

def parse_magma_codes(path):
    """Parse a Magma file containing a list of LinearCode<GF(2),n| rows > blocks.
    Returns list of (n, rows) with rows as lists of 0/1 lists."""
    txt = open(path).read()
    out = []
    for m in re.finditer(r"LinearCode<GF\(2\),(\d+)\|(.*?)>", txt, re.S):
        n = int(m.group(1))
        body = m.group(2)
        rows = []
        for r in re.finditer(r"\[([01,\s]*)\]", body):
            vals = [int(t) for t in r.group(1).replace("\n", "").split(",") if t.strip() != ""]
            assert len(vals) == n, (len(vals), n)
            rows.append(vals)
        out.append((n, rows))
    return out

def row_to_int(row):
    v = 0
    for i, b in enumerate(row):
        if b:
            v |= 1 << i
    return v

def int_to_row(v, n):
    return [(v >> i) & 1 for i in range(n)]

def echelon(vecs):
    """Return reduced basis (list of ints) with distinct leading bits (pivot = highest bit)."""
    basis = []  # list of (pivot, vec)
    for v in vecs:
        for p, b in basis:
            if (v >> p) & 1:
                v ^= b
        if v:
            p = v.bit_length() - 1
            # reduce existing
            nb = []
            for q, b in basis:
                if (b >> p) & 1:
                    b ^= v
                nb.append((q, b))
            basis = nb + [(p, v)]
    return [b for _, b in basis]

def rank(vecs):
    return len(echelon(vecs))

def in_span(v, basis_pairs):
    for p, b in basis_pairs:
        if (v >> p) & 1:
            v ^= b
    return v == 0

class Span:
    """Incremental span with reduction."""
    def __init__(self, vecs=()):
        self.piv = []  # list of (p, b), sorted not required
        for v in vecs:
            self.add(v)
    def reduce(self, v):
        for p, b in self.piv:
            if (v >> p) & 1:
                v ^= b
        return v
    def add(self, v):
        v = self.reduce(v)
        if v:
            self.piv.append((v.bit_length() - 1, v))
            return True
        return False
    def contains(self, v):
        return self.reduce(v) == 0
    def dim(self):
        return len(self.piv)
    def basis(self):
        return [b for _, b in self.piv]

def all_codewords(basis):
    """Gray-code enumeration of all 2^k codewords (generator)."""
    k = len(basis)
    c = 0
    yield c
    for i in range(1, 1 << k):
        # bit that changes: lowest set bit of i
        j = (i & -i).bit_length() - 1
        c ^= basis[j]
        yield c

def dual_basis(basis, n):
    """Basis of the dual code (ints) of span(basis) in GF(2)^n."""
    # Gaussian elimination to RREF with pivot columns
    rows = list(basis)
    piv_cols = []
    r = 0
    rows = [x for x in rows]
    m = len(rows)
    for col in range(n):
        sel = None
        for i in range(r, m):
            if (rows[i] >> col) & 1:
                sel = i
                break
        if sel is None:
            continue
        rows[r], rows[sel] = rows[sel], rows[r]
        for i in range(m):
            if i != r and (rows[i] >> col) & 1:
                rows[i] ^= rows[r]
        piv_cols.append(col)
        r += 1
        if r == m:
            break
    rows = rows[:r]
    free = [c for c in range(n) if c not in piv_cols]
    out = []
    for f in free:
        v = 1 << f
        for i, pc in enumerate(piv_cols):
            if (rows[i] >> f) & 1:
                v |= 1 << pc
        out.append(v)
    return out

def dot(x, y):
    return popcount(x & y) & 1

def span_array(basis):
    """All codewords of span(basis) as a numpy uint64 array (len 2^k), k <= ~26."""
    import numpy as np
    arr = np.zeros(1, dtype=np.uint64)
    for b in basis:
        arr = np.concatenate([arr, arr ^ np.uint64(b)])
    return arr

def popcount_array(a):
    import numpy as np
    a = a.astype(np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    for sh in range(0, 64, 16):
        c += _POP16[((a >> np.uint64(sh)) & np.uint64(0xFFFF)).astype(np.int64)]
    return c

def _mk_pop16():
    import numpy as np
    t = np.zeros(1 << 16, dtype=np.int64)
    for i in range(1, 1 << 16):
        t[i] = t[i >> 1] + (i & 1)
    return t
_POP16 = _mk_pop16()

def weight_distribution(basis, n):
    import numpy as np
    w = popcount_array(span_array(basis))
    return np.bincount(w, minlength=n + 1)
