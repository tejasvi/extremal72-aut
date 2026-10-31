"""GF(2) linear algebra on Python ints."""


class Elim:
    """Incremental reduced row echelon basis with combination tracking.
    add(v, tag) adds vector v (int) labelled by tag-bit; express(v) returns (combo, residual)."""

    def __init__(self):
        self.rows = {}  # pivot -> (vec, combo)

    def reduce(self, v, c=0):
        for p, (r, rc) in self.rows.items():
            if v >> p & 1:
                v ^= r
                c ^= rc
        return v, c

    def add(self, v, c):
        """returns True if independent (then added with pivot = highest bit)."""
        v, c = self.reduce(v, c)
        if not v:
            return False, c
        p = v.bit_length() - 1
        for q, (r, rc) in list(self.rows.items()):
            if r >> p & 1:
                self.rows[q] = (r ^ v, rc ^ c)
        self.rows[p] = (v, c)
        return True, c

    def express(self, v):
        """combo of added tags whose XOR equals v - residual; residual==0 iff v in span."""
        return self.reduce(v, 0)[::-1]

    def __len__(self):
        return len(self.rows)


def solve(funcs, targets):
    """Find int v with parity(popcount(f & v)) = t for all (f,t); None if inconsistent.
    Works by transposed elimination: we need v in the 'column' space; do elimination on (f | t)."""
    rows = []  # list of (f, t) reduced, pivot = lowest set bit of f
    for f, t in zip(funcs, targets):
        for (r, rt) in rows:
            p = (r & -r).bit_length() - 1
            if f >> p & 1:
                f ^= r
                t ^= rt
        if f == 0:
            if t:
                return None
            continue
        p = (f & -f).bit_length() - 1
        rows = [((r ^ f), rt ^ t) if r >> p & 1 else (r, rt) for (r, rt) in rows]
        rows.append((f, t))
    v = 0
    for (r, rt) in rows:
        if rt:
            v |= r & -r  # set the pivot bit; pivots are unique to their row (fully reduced)
    for f, t in zip(funcs, targets):
        assert bin(f & v).count("1") & 1 == t
    return v
