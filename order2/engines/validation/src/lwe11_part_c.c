// ---- lwe11: fast level filter (AVX-512 VBMI + GFNI) ----
// Per level t the constraints get lanes in processing order: rank-0 constraints first (whole node), then the
// translate constraints, then the rest (checked child by child).  s0 of every lane is one uint16 vector
// P[t] = fc ^ sum_{l<t} row_l(x_l), kept along the path: P[e] = P[e-1] ^ (chunk rows of x_{e-1}), stamped nid[e].
// Translate constraint: bad children of s0 = base[coset(s0)] XOR-translated by v0(s0), where
// s0 = crep ^ L v0 (reduction modulo Im L); (coset, v0) = cvlo[s0 & 255] ^ cvhi[s0 >> 8] (the reduction is linear).
typedef struct {
    const uint32_t *cvlo, *cvhi;      // (coset << 16) | v0
    const uint8_t *base;              // one bitmap of 'stride' = 1 << sh bytes per coset of Im L (+64 bytes padding)
    const uint16_t *vlo, *vhi;        // L x = vlo[x & 255] ^ vhi[x >> 8] (list mode, kt >= 10)
    int sh;
} FC;
typedef struct {
    int on, kt, nbytes, nz, nwords, nc, npad, nr0, ntr, vec, thr;
    int *cid;                         // constraint index per lane
    FC *fc;                           // translate records for lanes nr0 .. nr0+ntr-1
    uint16_t *PB; unsigned long long *PBst;
    uint16_t *chunk[40][4];           // chunk[l][q]: 16 rows of npad lanes (bits 4q..4q+3 of x_l)
    u64 *allm;                        // nz*8 words: low 2^kt bits set
} LV;
static LV LVL[40];
static int nchunk[41];
static u64 xv[41];                    // value of level l on the current path
static unsigned char lhact[42];       // lh_reject can return 1 at level t
static __m512i IOTA;
static u64 AFF[8];
static int CHECK = 0;                 // LWE11CHECK: verify s0 vectors and alive sets against a direct computation
static long long fastnodes = 0, checknodes = 0;

static void *amalloc(size_t n) { void *p = aligned_alloc(64, (n + 63) / 64 * 64 + 64); if (!p) die("alloc"); memset(p, 0, (n + 63) / 64 * 64 + 64); return p; }
static inline uint32_t colL(const Con *X, int l, int j) {   // syndrome column of variable j of level l
    uint32_t v = 0; for (int s = 0; s < X->m; s++) v |= (uint32_t)((X->fm[s] >> (vstart[l] + j)) & 1) << s; return v;
}
static uint32_t reduce_cv(const Con *X, uint32_t s0) {      // (coset index << 16) | v0 with s0 = crep ^ L v0
    uint32_t sv = s0, v0 = 0;
    for (int q = 0; q < X->irank; q++) if ((sv >> X->ipiv[q]) & 1) { sv ^= X->ivec[q]; v0 ^= X->ipre[q]; }
    uint32_t ci = 0; for (int q = 0; q < X->m - X->irank; q++) if ((sv >> X->cbits[q]) & 1) ci |= 1u << q;
    return (ci << 16) | v0;
}
static void build_fast(void) {
    for (int j = 0; j < 8; j++) { u64 A = 0; for (int i = 0; i < 8; i++) A |= (u64)(1u << (i ^ j)) << (8 * (7 - i)); AFF[j] = A; }
    { uint8_t io[64]; for (int i = 0; i < 64; i++) io[i] = (uint8_t)i; IOTA = _mm512_loadu_si512(io); }
    for (int l = 0; l <= NLEV; l++) { int k = (l < NLEV) ? vstart[l + 1] - vstart[l] : 0; nchunk[l] = (k + 3) / 4; }
    const char *thr = getenv("LWE11THR");
    long tbytes = 0, vbytes = 0; long vbudget = 24L << 20;
    for (int t = 0; t < NLEV; t++) {
        LV *L = &LVL[t]; memset(L, 0, sizeof(LV));
        int kt = vstart[t + 1] - vstart[t];
        if (kt > 16 || getenv("LWE11OFF")) continue;
        L->kt = kt; L->nbytes = kt >= 3 ? 1 << (kt - 3) : 1; L->nz = L->nbytes >= 64 ? L->nbytes / 64 : 1;
        L->nwords = kt >= 6 ? 1 << (kt - 6) : 1;
        L->thr = thr ? atoi(thr) : (L->nz <= 2 ? 0 : 4 * L->nz);
        int nc = lstart[t + 1] - lstart[t]; L->nc = nc; L->npad = (nc + 31) / 32 * 32; if (L->npad == 0) L->npad = 32;
        L->cid = malloc(sizeof(int) * (nc + 1)); L->fc = calloc(nc + 1, sizeof(FC));
        // classify in ORD order: rank 0, translate (base fits), rest
        int *cls = malloc(sizeof(int) * (nc + 1));
        for (int i = 0; i < nc; i++) {
            Con *X = &C[ORD[lstart[t] + i]];
            if (X->rank == 0) cls[i] = 0;
            else { long ncos = 1L << (X->m - X->irank); cls[i] = (ncos * L->nbytes <= 32768) ? 1 : 2; }
        }
        int pos = 0;
        for (int k = 0; k < 3; k++) for (int i = 0; i < nc; i++) if (cls[i] == k) L->cid[pos++] = ORD[lstart[t] + i];
        L->nr0 = 0; L->ntr = 0; for (int i = 0; i < nc; i++) { if (cls[i] == 0) L->nr0++; if (cls[i] == 1) L->ntr++; }
        free(cls);
        for (int i = L->nr0; i < L->nr0 + L->ntr; i++) {
            Con *X = &C[L->cid[i]]; FC *F = &L->fc[i];
            int m = X->m; long ns = 1L << m; int sh = 0; while ((1 << sh) < L->nbytes) sh++;
            F->sh = sh;
            uint32_t *lo = malloc(sizeof(uint32_t) * 256), *hi = malloc(sizeof(uint32_t) * (ns > 256 ? ns >> 8 : 1));
            for (long s = 0; s < 256; s++) lo[s] = (s < ns) ? reduce_cv(X, (uint32_t)s) : 0;
            hi[0] = 0; for (long h = 1; h < (ns >> 8); h++) hi[h] = reduce_cv(X, (uint32_t)(h << 8));
            for (long s = 0; s < ns; s++) if ((lo[s & 255] ^ hi[s >> 8]) != reduce_cv(X, (uint32_t)s)) die("cv not linear");
            F->cvlo = lo; F->cvhi = hi; tbytes += 4 * (256 + (ns > 256 ? ns >> 8 : 1));
            long ncos = 1L << (m - X->irank);
            uint8_t *B = amalloc((size_t)ncos * L->nbytes + 64);
            for (long ci = 0; ci < ncos; ci++) {
                uint32_t crep = 0; for (int q = 0; q < m - X->irank; q++) if ((ci >> q) & 1) crep |= 1u << X->cbits[q];
                uint8_t *b = B + ci * L->nbytes; uint32_t sv = crep;
                for (long v = 0; v < (1L << kt); v++) {
                    if (v) sv ^= X->col[__builtin_ctzl(v)];
                    long g = v ^ (v >> 1);
                    if ((X->badbm[sv >> 6] >> (sv & 63)) & 1) b[g >> 3] |= (uint8_t)(1u << (g & 7));
                }
            }
            F->base = B; tbytes += ncos * L->nbytes;
            if (kt >= 10) {
                uint16_t *vl = malloc(sizeof(uint16_t) * 256), *vh = malloc(sizeof(uint16_t) * (1 << (kt - 8)));
                for (int x = 0; x < 256; x++) { uint32_t a = 0; for (int j = 0; j < 8 && j < kt; j++) if ((x >> j) & 1) a ^= X->col[j]; vl[x] = (uint16_t)a; }
                for (int x = 0; x < (1 << (kt - 8)); x++) { uint32_t a = 0; for (int j = 0; j < kt - 8; j++) if ((x >> j) & 1) a ^= X->col[8 + j]; vh[x] = (uint16_t)a; }
                F->vlo = vl; F->vhi = vh;
            }
        }
        L->allm = amalloc(sizeof(u64) * L->nz * 8);
        for (long v = 0; v < (1L << kt); v++) L->allm[v >> 6] |= 1ULL << (v & 63);
        // s0 vector chain
        long need = 0; for (int l = 0; l < t; l++) need += (long)nchunk[l] * 16 * L->npad * 2;
        need += (long)(t + 1) * L->npad * 2;
        if (need <= (4L << 20) && vbytes + need <= vbudget) {
            L->vec = 1; vbytes += need;
            L->PB = amalloc(sizeof(uint16_t) * (size_t)(t + 1) * L->npad); L->PBst = calloc(t + 1, sizeof(unsigned long long));
            for (int i = 0; i < nc; i++) { const Con *X = &C[L->cid[i]]; uint32_t f = 0; for (int s = 0; s < X->m; s++) f |= (uint32_t)X->fc[s] << s; L->PB[i] = (uint16_t)f; }
            for (int l = 0; l < t; l++) {
                int k = vstart[l + 1] - vstart[l];
                for (int q = 0; q < nchunk[l]; q++) {
                    uint16_t *T = amalloc(sizeof(uint16_t) * 16 * L->npad); L->chunk[l][q] = T;
                    for (int i = 0; i < nc; i++) {
                        const Con *X = &C[L->cid[i]]; uint32_t cl[4];
                        for (int j = 0; j < 4; j++) cl[j] = (4 * q + j < k) ? colL(X, l, 4 * q + j) : 0;
                        for (int r = 0; r < 16; r++) { uint32_t a = 0; for (int j = 0; j < 4; j++) if ((r >> j) & 1) a ^= cl[j]; T[(size_t)r * L->npad + i] = (uint16_t)a; }
                    }
                }
            }
        }
        L->on = 1;
    }
    if (LH) {
        int lv0 = C[LHc0].lv;
        for (int t = 0; t <= NLEV; t++) {
            int a = 0;
            if (t - 1 >= lv0) {
                if (lv0 == t - 1) a = 1;
                for (int u = 0; u < LHnO; u++) { int lu = C[LHuc[u]].lv > lv0 ? C[LHuc[u]].lv : lv0; if (lu == t - 1) a = 1; }
                if (LHr >= 2) { if (t >= 32) a = 1; else for (int g = 0; g < LHnG; g++) if ((LHtrig[g] >> t) & 1) a = 1; }
            }
            lhact[t] = (unsigned char)a;
        }
        if (getenv("LWE11NOSKIP")) for (int t = 0; t <= NLEV; t++) lhact[t] = 1;
    }
    if (getenv("LWE11VERB")) {
        fprintf(stderr, "lwe11: translate tables %.2f MB, s0 vector tables %.2f MB\n", tbytes / 1048576.0, vbytes / 1048576.0);
        for (int t = 0; t < NLEV; t++) { LV *L = &LVL[t]; fprintf(stderr, " L%d on %d kt %d nc %d r0 %d tr %d rest %d vec %d thr %d lhact %d\n", t, L->on, L->kt, L->nc, L->nr0, L->ntr, L->nc - L->nr0 - L->ntr, L->vec, L->thr, lhact[t]); }
    }
}
static inline const uint16_t *s0vec(LV *L, int t) {
    int e = t;
    while (e > 0 && L->PBst[e] != nid[e]) e--;
    const int np = L->npad;
    for (int f = e + 1; f <= t; f++) {
        const int l = f - 1, nq = nchunk[l]; const unsigned x = (unsigned)xv[l];
        const uint16_t *src = L->PB + (size_t)(f - 1) * np; uint16_t *dst = L->PB + (size_t)f * np;
        const uint16_t *r0 = nq > 0 ? L->chunk[l][0] + (size_t)(x & 15) * np : NULL;
        const uint16_t *r1 = nq > 1 ? L->chunk[l][1] + (size_t)((x >> 4) & 15) * np : NULL;
        const uint16_t *r2 = nq > 2 ? L->chunk[l][2] + (size_t)((x >> 8) & 15) * np : NULL;
        const uint16_t *r3 = nq > 3 ? L->chunk[l][3] + (size_t)((x >> 12) & 15) * np : NULL;
        for (int i = 0; i < np; i += 32) {
            __m512i a = _mm512_load_si512((const void *)(src + i));
            if (nq > 0) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r0 + i)));
            if (nq > 1) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r1 + i)));
            if (nq > 2) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r2 + i)));
            if (nq > 3) a = _mm512_xor_si512(a, _mm512_load_si512((const void *)(r3 + i)));
            _mm512_store_si512((void *)(dst + i), a);
        }
        L->PBst[f] = nid[f];
    }
    return L->PB + (size_t)t * np;
}
static inline uint32_t lane_s0(LV *L, const uint16_t *S, int i) { return L->vec ? S[i] : (uint32_t)syn0(&C[L->cid[i]]); }
static inline int bad_child(const Con *X, uint32_t s0, uint32_t v) {
    uint32_t sv = s0; while (v) { sv ^= X->col[__builtin_ctz(v)]; v &= v - 1; }
    return (int)((X->badbm[sv >> 6] >> (sv & 63)) & 1);
}
static void check_node(LV *L, int t, const uint16_t *S, const u64 *alive, int dead) {   // LWE11CHECK
    checknodes++;
    if (L->vec) for (int i = 0; i < L->nc; i++) if (S[i] != (uint16_t)syn0_plain(&C[L->cid[i]])) { fprintf(stderr, "CHECK s0 mismatch level %d lane %d\n", t, i); exit(3); }
    for (long v = 0; v < (1L << L->kt); v++) {
        int ok = 1;
        for (int i = 0; i < L->nc && ok; i++) { const Con *X = &C[L->cid[i]]; if (bad_child(X, (uint32_t)syn0_plain(X), (uint32_t)v)) ok = 0; }
        int got = dead ? 0 : (int)((alive[v >> 6] >> (v & 63)) & 1);
        if (ok != got) { fprintf(stderr, "CHECK alive mismatch level %d child %ld: direct %d fast %d\n", t, v, ok, got); exit(3); }
    }
}
static void search(int t);
static void kids_loop(int t, const u64 *w, int nwords) {
    u128 clearmask = ~(((((u128)1) << (vstart[t + 1] - vstart[t])) - 1) << vstart[t]);
    if (probe_mode) {
        long cnt = 0; for (int i = 0; i < nwords; i++) cnt += __builtin_popcountll(w[i]);
        if (!cnt) return;
        long pick = (long)(rnd64() % (unsigned long long)cnt);
        for (int i = 0; i < nwords; i++) { long c = __builtin_popcountll(w[i]); if (pick < c) { u64 b = w[i]; for (long q = 0; q < pick; q++) b &= b - 1; long v = ((long)i << 6) + __builtin_ctzll(b);
                    probe_w *= (double)cnt; est[t + 1] += probe_w;
                    asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v; search(t + 1); asg &= clearmask; return; } pick -= c; }
        return;
    }
    for (int i = 0; i < nwords; i++) {
        u64 bits = w[i];
        while (bits) {
            int j = __builtin_ctzll(bits); bits &= bits - 1;
            long v = ((long)i << 6) + j;
            kids[t]++;
            asg = (asg & clearmask) | (((u128)v) << vstart[t]); xv[t] = (u64)v;
            search(t + 1);
        }
    }
    asg &= clearmask;
}
static void search_fast(int t) {
    LV *L = &LVL[t];
    fastnodes++;
    const uint16_t *S = L->vec ? s0vec(L, t) : NULL;
    const int nr0 = L->nr0, ntr = L->ntr, nc = L->nc;
    for (int i = 0; i < nr0; i++) { uint32_t s = lane_s0(L, S, i); if ((C[L->cid[i]].badbm[s >> 6] >> (s & 63)) & 1) { if (CHECK) check_node(L, t, S, NULL, 1); return; } }
    if (L->nz == 1) {
        __m512i al = _mm512_load_si512((const void *)L->allm);
        for (int i = nr0; i < nr0 + ntr; i++) {
            const FC *F = &L->fc[i];
            uint32_t s = lane_s0(L, S, i);
            uint32_t e = F->cvlo[s & 255] ^ F->cvhi[s >> 8];
            __m512i B = _mm512_loadu_si512((const void *)(F->base + ((size_t)(e >> 16) << F->sh)));
            B = _mm512_permutexvar_epi8(_mm512_xor_si512(IOTA, _mm512_set1_epi8((char)((e >> 3) & 63))), B);
            B = _mm512_gf2p8affine_epi64_epi8(B, _mm512_set1_epi64((long long)AFF[e & 7]), 0);
            al = _mm512_andnot_si512(B, al);
            if (!_mm512_test_epi64_mask(al, al)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        u64 w[8] __attribute__((aligned(64)));
        _mm512_store_si512((void *)w, al);
        for (int i = nr0 + ntr; i < nc; i++) {           // rest: child by child
            const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
            for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
            if (!any) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop(t, w, L->nwords);
        return;
    }
    // multi-ZMM bitmaps (kt >= 10), list mode below L->thr survivors
    const int nz = L->nz;
    __m512i A[128];
    for (int z = 0; z < nz; z++) A[z] = _mm512_load_si512((const void *)(L->allm + 8 * z));
    int i = nr0;
    uint32_t list[64]; int nlist = -1;
    for (; i < nr0 + ntr; i++) {
        const FC *F = &L->fc[i];
        uint32_t s = lane_s0(L, S, i);
        uint32_t e = F->cvlo[s & 255] ^ F->cvhi[s >> 8];
        const uint8_t *bp = F->base + ((size_t)(e >> 16) << F->sh);
        const __m512i idx = _mm512_xor_si512(IOTA, _mm512_set1_epi8((char)((e >> 3) & 63)));
        const __m512i M = _mm512_set1_epi64((long long)AFF[e & 7]);
        const int Z = (int)((e & 0xFFFF) >> 9);
        __m512i any = _mm512_setzero_si512();
        for (int z = 0; z < nz; z++) {
            __m512i B = _mm512_loadu_si512((const void *)(bp + ((size_t)(z ^ Z) << 6)));
            B = _mm512_gf2p8affine_epi64_epi8(_mm512_permutexvar_epi8(idx, B), M, 0);
            A[z] = _mm512_andnot_si512(B, A[z]);
            any = _mm512_or_si512(any, A[z]);
        }
        if (!_mm512_test_epi64_mask(any, any)) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        if (L->thr > 0) {
            long cnt = 0; for (int z = 0; z < nz; z++) cnt += _mm512_reduce_add_epi64(_mm512_popcnt_epi64(A[z]));
            if (cnt <= L->thr) {
                u64 w[8] __attribute__((aligned(64))); nlist = 0;
                for (int z = 0; z < nz; z++) { _mm512_store_si512((void *)w, A[z]); for (int k = 0; k < 8; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; list[nlist++] = (uint32_t)((z << 9) + (k << 6) + j); } } }
                i++; break;
            }
        }
    }
    if (nlist >= 0) {
        for (; i < nr0 + ntr; i++) {
            const FC *F = &L->fc[i]; const u64 *bb = C[L->cid[i]].badbm;
            uint32_t s = lane_s0(L, S, i); int nl = 0;
            for (int q = 0; q < nlist; q++) {
                uint32_t x = list[q]; uint32_t sv = s ^ F->vlo[x & 255] ^ F->vhi[x >> 8];
                int bad = (int)((bb[sv >> 6] >> (sv & 63)) & 1);
                list[nl] = x; nl += 1 - bad;
            }
            nlist = nl; if (!nlist) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        for (; i < nc; i++) {
            const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int nl = 0;
            for (int q = 0; q < nlist; q++) { uint32_t x = list[q]; int bad = bad_child(X, s, x); list[nl] = x; nl += 1 - bad; }
            nlist = nl; if (!nlist) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
        }
        u64 w[128 * 8] __attribute__((aligned(64)));
        memset(w, 0, sizeof(u64) * L->nwords);
        for (int q = 0; q < nlist; q++) w[list[q] >> 6] |= 1ULL << (list[q] & 63);   // list is in increasing order
        if (CHECK) check_node(L, t, S, w, 0);
        kids_loop(t, w, L->nwords);
        return;
    }
    u64 w[128 * 8] __attribute__((aligned(64)));
    for (int z = 0; z < nz; z++) _mm512_store_si512((void *)(w + 8 * z), A[z]);
    for (; i < nc; i++) {
        const Con *X = &C[L->cid[i]]; uint32_t s = lane_s0(L, S, i); int any = 0;
        for (int k = 0; k < L->nwords; k++) { u64 b = w[k]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; if (bad_child(X, s, (uint32_t)((k << 6) + j))) w[k] &= ~(1ULL << j); } any |= (w[k] != 0); }
        if (!any) { if (CHECK) check_node(L, t, S, NULL, 1); return; }
    }
    if (CHECK) check_node(L, t, S, w, 0);
    kids_loop(t, w, L->nwords);
}
static void search(int t) {
    nid[t] = ++NIDC;
    if (t == NLEV) {
        if (SYM && sym_reject(t)) { symprune[t]++; return; }
        if (LR && ltsr_reject(t)) { ltsprune[t]++; return; }
        if (LH && lh_reject(t)) { lhprune[t]++; return; }
        nsol++;
        printf("SOLUTION %016llx%016llx\n", (unsigned long long)(asg >> 64), (unsigned long long)asg); fflush(stdout);
        return;
    }
    nodes[t]++;
    if (stopflag) return;
    if (SYM && sym_reject(t)) { symprune[t]++; return; }
    if (LR && ltsr_reject(t)) { ltsprune[t]++; return; }
    if (LH && lhact[t] && lh_reject(t)) { lhprune[t]++; return; }
    if (t == SPL) { long long id = splitcnt++; if (id % NPART != PART) return; }
    if (LVL[t].on) { search_fast(t); return; }
    int kt = vstart[t + 1] - vstart[t];
    long nch = 1L << kt; int nw = (int)((nch + 63) / 64);
    u64 *A = alive[t];
    for (int i = 0; i < nw; i++) A[i] = ~0ULL;
    if (nch % 64) A[nw - 1] = (1ULL << (nch % 64)) - 1;
    int listmode = 0; int nlist = 0; uint32_t list[64];
    for (int ci = lstart[t]; ci < lstart[t + 1]; ci++) {
        Con *X = &C[ORD[ci]];
        int s0 = syn0(X);
        if (listmode) {
            if (X->method == 2) { if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return; continue; }
            int nl = 0;
            if (X->V) {
                const uint16_t *V = X->V; const u64 *bb = X->badbm;
                for (int q = 0; q < nlist; q++) {      // branch-free compaction
                    uint32_t x = list[q]; int sv = s0 ^ V[x];
                    int bad = (int)((bb[sv >> 6] >> (sv & 63)) & 1);
                    list[nl] = x; nl += 1 - bad;
                }
            } else
            for (int q = 0; q < nlist; q++) {
                uint32_t v = list[q]; int sv = s0;
                while (v) { int j = __builtin_ctz(v); v &= v - 1; sv ^= X->col[j]; }
                if (!((X->badbm[sv >> 6] >> (sv & 63)) & 1)) list[nl++] = list[q];
            }
            nlist = nl; if (!nlist) return;
            continue;
        }
        if (X->method == 2) {            // fully determined by lower levels
            if ((X->badbm[s0 >> 6] >> (s0 & 63)) & 1) return;
            continue;
        }
        if (X->tb) {
            // reduce s0 modulo Im L: s0 ^ L v0 = crep (coset rep), then bad children = base_crep translated by v0
            uint32_t sv = (uint32_t)s0, v0 = 0;
            for (int q = 0; q < X->irank; q++) { uint32_t mk = 0u - ((sv >> X->ipiv[q]) & 1u); sv ^= X->ivec[q] & mk; v0 ^= X->ipre[q] & mk; }
            long ci2 = 0;
            for (int q = 0; (1L << q) < X->ncos; q++) if ((sv >> X->cbits[q]) & 1) ci2 |= 1L << q;
            u64 *tmp = tmpbuf;
            const u64 *Bm = X->base + ci2 * nw;
            if (nch < 64) { u64 w = Bm[0]; u64 o = w; uint32_t d = v0; o = w;
                for (int j = 0; j < 6; j++) { int sh = 1 << j; u64 M = TMASK[j]; u64 mk = 0ULL - (u64)((d >> j) & 1); u64 sw = ((o & M) << sh) | ((o >> sh) & M); o = (o & ~mk) | (sw & mk); }
                A[0] &= ~o; }
            else { xor_translate(tmp, Bm, nw, v0); for (int i = 0; i < nw; i++) A[i] &= ~tmp[i]; }
        } else if (X->method == 0) {
            int s = s0;
            for (long v = 0; v < nch; v++) {
                if (v) { int j = __builtin_ctzl(v); s ^= X->col[j]; }
                long g = v ^ (v >> 1);    // Gray code index whose syndrome is s
                if ((X->badbm[s >> 6] >> (s & 63)) & 1) A[g >> 6] &= ~(1ULL << (g & 63));
            }
        } else {
            for (int k = 0; k < X->nbad; k++) {
                int r = X->bad[k] ^ s0; int ok = 1;
                for (int z = 0; z < X->nz; z++) if (__builtin_popcount(X->Z[z] & r) & 1) { ok = 0; break; }
                if (!ok) continue;
                uint32_t v0 = 0;
                for (int i = 0; i < X->rank; i++) if (__builtin_popcount(X->T[i] & r) & 1) v0 |= 1u << X->pivc[i];
                uint32_t v = v0;
                long nk = 1L << X->kdim;
                for (long q = 0; q < nk; q++) {
                    if (q) { int j = __builtin_ctzl(q); v ^= X->kb[j]; }
                    A[v >> 6] &= ~(1ULL << (v & 63));
                }
            }
        }
        // early exit if nothing alive; switch to list mode when few children remain
        long cnt = 0; for (int i = 0; i < nw; i++) cnt += __builtin_popcountll(A[i]);
        if (!cnt) return;
        if (cnt <= 48) {
            listmode = 1; nlist = 0;
            for (int i = 0; i < nw; i++) { u64 b = A[i]; while (b) { int j = __builtin_ctzll(b); b &= b - 1; list[nlist++] = (uint32_t)(((long)i << 6) + j); } }
        }
    }
    if (listmode) {   // rebuild the alive bitmap from the list
        for (int i = 0; i < nw; i++) A[i] = 0;
        for (int q = 0; q < nlist; q++) A[list[q] >> 6] |= 1ULL << (list[q] & 63);
    }
    kids_loop(t, A, nw);
}
