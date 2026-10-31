"""Prepare engine data: variables = an ordered basis of gauge-invariant functionals (mod the diagonal constraints);
constraints = low-weight words with their syndromes expressed in the variables."""
import sys, struct
sys.path.insert(0, "<HOME>/c72_indep/y22/src")
from problem import *
from linalg import Elim, solve


def parity(x):
    return bin(x).count("1") & 1


class EngineData:
    def __init__(self, P, word_order, Rmax=3, extra_var_funcs=()):
        """word_order: list of low-weight words; variables are selected greedily from extra_var_funcs first,
        then from the syndrome functionals of words in this order."""
        self.P = P
        FS = P.FS
        nd = len(P.diag)
        # elimination over [diag | vars]; tags: bit t for diag t (t < nd), bit nd + i for var i
        E = Elim()
        for t, (f, c) in enumerate(P.diag):
            E.add(f, 1 << t)
        self.var_funcs = []
        self.word_info = {}
        for y in P.low:
            xb = P.shortened_basis(y)
            self.word_info[y] = (xb, [FS.functional(y, x) for x in xb])
        cands = list(extra_var_funcs)
        seen0 = set(word_order)
        for y in list(word_order) + [y for y in P.low if y not in seen0]:
            cands += self.word_info[y][1]
        for f in cands:
            ok, _ = E.add(f, 1 << (nd + len(self.var_funcs)))
            if ok:
                self.var_funcs.append(f)
        self.nv = len(self.var_funcs)
        self.E = E
        self.nd = nd
        diag_const = 0
        for t, (f, c) in enumerate(P.diag):
            if c:
                diag_const |= 1 << t
        # words: in the order of word_order first, then any remaining low words
        seen = set(word_order)
        self.words = list(word_order) + [y for y in P.low if y not in seen]
        self.wdata = []
        for y in self.words:
            xb, fs = self.word_info[y]
            rows, const = [], 0
            for j, f in enumerate(fs):
                combo, resid = E.express(f)
                assert resid == 0, "syndrome functional not in span"
                rows.append(combo >> nd)
                if parity(combo & diag_const & ((1 << nd) - 1)):
                    const |= 1 << j
            forb = P.forbidden_syndromes(y, xb)
            self.wdata.append((y, rows, const, forb))
        self.Rmax = Rmax
        self._events()

    def _events(self):
        """For each word and each depth d at which the rank of the free part drops (d variables assigned, the
        possible syndromes form the coset s + V_d, V_d = column space of the unassigned variables), record the
        set of 'dead' cosets (all elements forbidden); keep the event only if some coset is dead."""
        nv = self.nv
        self.events = []  # (d, word index, basis of V_d (fully reduced, pivot = lowest bit), dead reps set)
        self.full_depth = []
        for wi, (y, rows, const, forb) in enumerate(self.wdata):
            m = len(rows)
            cols = [sum(((rows[j] >> i) & 1) << j for j in range(m)) for i in range(nv)]
            ech = []
            ranks = [0] * (nv + 1)
            bases = [None] * (nv + 1)
            bases[nv] = []
            for d in range(nv - 1, -1, -1):
                v = cols[d]
                for r in ech:
                    if v >> ((r & -r).bit_length() - 1) & 1:
                        v ^= r
                if v:
                    p = v & -v
                    ech = [r ^ v if r & p else r for r in ech]
                    ech.append(v)
                ranks[d] = len(ech)
                bases[d] = list(ech)
            dfull = max([i + 1 for i in range(nv) if cols[i]] + [0])
            self.full_depth.append(dfull)
            for d in range(0, nv + 1):
                if d > 0 and ranks[d - 1] == ranks[d]:
                    continue
                basis = bases[d]
                r = len(basis)
                cnt = {}
                for s in forb:
                    t = s
                    for b in basis:
                        if t >> ((b & -b).bit_length() - 1) & 1:
                            t ^= b
                    cnt[t] = cnt.get(t, 0) + 1
                dead = {t for t, c in cnt.items() if c == (1 << r)}
                if dead:
                    self.events.append((d, wi, basis, dead))
        self.events.sort(key=lambda e: (e[0], len(e[2]), e[1]))

    def write(self, path):
        """Binary format (little endian):
        header: magic 'Y39F', nv, nwords, nevents
        words: for each: m, const(uint32), m rows x 2 uint64
        events: d, word, r (int32 each), r x uint32 basis vectors (fully reduced, pivot = lowest set bit),
                dead bitmap over F2^m (bytes = max(1, 2^m/8)), indexed by reduced representatives
        """
        with open(path, "wb") as f:
            f.write(b"Y39F")
            f.write(struct.pack("<iii", self.nv, len(self.wdata), len(self.events)))
            for (y, rows, const, forb) in self.wdata:
                m = len(rows)
                f.write(struct.pack("<iI", m, const))
                for r in rows:
                    f.write(struct.pack("<QQ", r & ((1 << 64) - 1), r >> 64))
            for (d, wi, basis, dead) in self.events:
                m = len(self.wdata[wi][1])
                f.write(struct.pack("<iii", d, wi, len(basis)))
                for b in basis:
                    f.write(struct.pack("<I", b))
                nb = max(1, (1 << m) // 8)
                bm = bytearray(nb)
                for t in dead:
                    bm[t >> 3] |= 1 << (t & 7)
                f.write(bytes(bm))

    # ---------- helpers for decoding solutions ----------
    def form_from_vars(self, vals):
        """vals: int (bit i = value of var i) -> Gram matrix M of a valid form with these variable values."""
        funcs = [f for f, c in self.P.diag] + self.var_funcs
        tg = [c for f, c in self.P.diag] + [(vals >> i) & 1 for i in range(self.nv)]
        v = solve(funcs, tg)
        assert v is not None
        M = self.P.vec_to_gram(v)
        assert self.P.is_valid_form(M)
        return M

    def vars_from_form(self, M):
        v = self.P.gram_to_vec(M)
        return sum(parity(f & v) << i for i, f in enumerate(self.var_funcs))

    def check_form(self, M):
        """Direct check of all syndrome conditions (independent of the variable encoding)."""
        P = self.P
        bad = []
        for (y, rows, const, forb) in self.wdata:
            xb = self.word_info[y][0]
            s = sum(P.B(M, y, x) << j for j, x in enumerate(xb))
            if s in forb:
                bad.append(y)
        return bad
