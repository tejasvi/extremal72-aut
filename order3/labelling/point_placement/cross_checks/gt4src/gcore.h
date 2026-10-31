/* Shared core for the Golay-labelling tests: forbidden 8-/12-set bitmaps over all 2^24 masks, the growing
   doubly-even code K (Omega in K, representatives with bit 23 clear), covered 5-sets, candidate octads through a
   5-set by syndromes, the generic octad-growth search, and solution hashing (RREF basis, FNV-1a). */
#ifndef GCORE_H
#define GCORE_H
#include "f4code.h"
#include "golay.h"
#include <immintrin.h>
#include <time.h>

static uint8_t *forb8, *forb12, *cov5;     /* compact bitmaps indexed by combinatorial rank of the subset */
#define GETB(bm, m) (((bm)[(m) >> 3] >> ((m) & 7)) & 1)
#define SETB(bm, m) ((bm)[(m) >> 3] |= (uint8_t)(1u << ((m) & 7)))
#define CLRB(bm, m) ((bm)[(m) >> 3] &= (uint8_t)~(1u << ((m) & 7)))
static uint32_t RK0[256], RK1[256][9], RK2[256][17];
static inline uint32_t srank(uint32_t m) {    /* rank of m among subsets of {0..23} of size popcount(m) */
    uint32_t b0 = m & 255, b1 = (m >> 8) & 255, b2 = m >> 16;
    int k0 = __builtin_popcount(b0), k1 = k0 + __builtin_popcount(b1);
    return RK0[b0] + RK1[b1][k0] + RK2[b2][k1];
}
#define F8(m) GETB(forb8, srank(m))
#define F12(m) GETB(forb12, srank(m))
#define SET8(m) SETB(forb8, srank(m))
#define SET12(m) SETB(forb12, srank(m))
#define COV5(m) GETB(cov5, srank(m))
#define F8BYTES ((735471 + 7) / 8)
#define F12BYTES ((2704156 + 7) / 8)
#define C5BYTES ((42504 + 7) / 8)
static uint32_t binom_(int n, int k) { if (k < 0 || k > n) return 0; uint64_t r = 1; for (int i = 1; i <= k; i++) r = r * (n - k + i) / i; return (uint32_t)r; }
static void rank_init(void) {
    for (int b = 0; b < 256; b++) {
        uint32_t r = 0; int idx = 0;
        for (int p = 0; p < 8; p++) if ((b >> p) & 1) { idx++; r += binom_(p, idx); }
        RK0[b] = r;
        for (int k = 0; k <= 8; k++) { uint32_t s = 0; int i = k; for (int p = 0; p < 8; p++) if ((b >> p) & 1) { i++; s += binom_(8 + p, i); } RK1[b][k] = s; }
        for (int k = 0; k <= 16; k++) { uint32_t s = 0; int i = k; for (int p = 0; p < 8; p++) if ((b >> p) & 1) { i++; s += binom_(16 + p, i); } RK2[b][k] = s; }
    }
}
static uint32_t pat5[56], pat4[70], pat3_19[969];

static uint32_t krep[2048];
static int nk, dim;
static uint32_t basis[13];
static uint32_t synd[24];
static long nodes[16], nsol, nchk;
#define MAXSOLSTORE 64
static uint32_t solbasis[MAXSOLSTORE][12]; static int nsolstore;
static uint64_t solhash;                 /* sum of hashes of all solutions (order independent) */

static void gcore_init(void) {
    int k = 0; for (uint32_t p = 0; p < 256; p++) if (__builtin_popcount(p) == 5) pat5[k++] = p;
    k = 0; for (uint32_t p = 0; p < 256; p++) if (__builtin_popcount(p) == 4) pat4[k++] = p;
    k = 0; for (uint32_t p = 0; p < (1u << 19); p++) if (__builtin_popcount(p) == 3) pat3_19[k++] = p;
    forb8 = calloc(F8BYTES, 1); forb12 = calloc(F12BYTES, 1); cov5 = calloc(C5BYTES, 1);
    rank_init();
}
static int use_cov5 = 0;          /* 0: coverage of 5-sets tested lazily against the words of K */
static inline int covered(uint32_t F) {
    if (use_cov5) return COV5(F);
    for (int j = 1; j < nk; j++) {
        uint32_t w = krep[j];
        int c = __builtin_popcount(w);
        if (c == 8) { if ((w & F) == F) return 1; }
        else if (c == 16) { if ((~w & F) == F) return 1; }
    }
    return 0;
}
static void mark_octad(uint32_t o, int on) {
    for (int i = 0; i < 56; i++) {
        uint32_t f = srank(_pdep_u32(pat5[i], o));
        if (on) SETB(cov5, f); else CLRB(cov5, f);
    }
}
static int addK(uint32_t O, uint32_t *buf) {
    uint32_t g = (O >> 23) ? (O ^ FULL24) : O;
    int m = 0;
    for (int j = 0; j < nk; j++) {
        uint32_t w = krep[j] ^ g;
        krep[nk + j] = w;
        int c = __builtin_popcount(w);
        if (c == 8) buf[m++] = w; else if (c == 16) buf[m++] = w ^ FULL24;
    }
    nk *= 2;
    for (int x = 0; x < 24; x++) synd[x] |= ((g >> x) & 1u) << (dim - 1);
    basis[dim++] = g;
    if (use_cov5) for (int i = 0; i < m; i++) mark_octad(buf[i], 1);
    return m;
}
static void undoK(uint32_t *buf, int m) {
    if (use_cov5) for (int i = 0; i < m; i++) mark_octad(buf[i], 0);
    nk /= 2; dim--;
    for (int x = 0; x < 24; x++) synd[x] &= ~(1u << (dim - 1));
}
static void resetK(void) {
    krep[0] = 0; nk = 1; dim = 1; basis[0] = FULL24; memset(synd, 0, sizeof synd); memset(cov5, 0, C5BYTES);
}
/* O: 8-set orthogonal to K, not in K.  Valid iff every new word of K + <O> has weight 8, 12 or 16, all octads
   (weight 8, or complements of weight 16) allowed and no forbidden dodecad (word or its complement). */
static inline int valid_new(uint32_t O) {
    nchk++;
    if (F8(O)) return 0;
    uint32_t g = (O >> 23) ? (O ^ FULL24) : O;
    for (int j = 1; j < nk; j++) {
        uint32_t w = krep[j] ^ g;
        int c = __builtin_popcount(w);
        if (c == 8) { if (F8(w)) return 0; }
        else if (c == 16) { if (F8(w ^ FULL24)) return 0; }
        else if (c == 12) { if (F12(w) || F12(w ^ FULL24)) return 0; }
        else return 0;
    }
    return 1;
}
static inline int orth(uint32_t O) {
    for (int i = 1; i < dim; i++) if (__builtin_parity(O & basis[i])) return 0;
    return 1;
}
/* all valid octads through the 5-set F (orthogonal to K), stop at lim.  Points bucketed by syndrome. */
static int16_t cand_head[4096];
static int cand_init = 0;
static int cands(uint32_t F, uint32_t *out, int lim) {
    if (!cand_init) { for (int i = 0; i < 4096; i++) cand_head[i] = -1; cand_init = 1; }
    uint32_t sF = 0;
    for (uint32_t t = F; t; t &= t - 1) sF ^= synd[__builtin_ctz(t)];
    int pts[19], np = 0; int8_t nxt[19];
    for (uint32_t t = FULL24 & ~F; t; t &= t - 1) pts[np++] = __builtin_ctz(t);
    for (int a = np - 1; a >= 0; a--) { uint32_t s = synd[pts[a]]; nxt[a] = (int8_t)cand_head[s]; cand_head[s] = (int16_t)a; }
    int c = 0;
    for (int a = 0; a < np && c < lim; a++) {
        uint32_t s1 = sF ^ synd[pts[a]];
        for (int b = a + 1; b < np && c < lim; b++) {
            uint32_t s2 = s1 ^ synd[pts[b]];
            for (int e = cand_head[s2]; e >= 0; e = nxt[e]) {
                if (e <= b) continue;
                uint32_t O = F | (1u << pts[a]) | (1u << pts[b]) | (1u << pts[e]);
                if (valid_new(O)) { out[c++] = O; if (c >= lim) break; }
            }
        }
    }
    for (int a = 0; a < np; a++) cand_head[synd[pts[a]]] = -1;
    return c;
}
static uint64_t code_hash(const uint32_t *B) {
    uint32_t R[12]; memcpy(R, B, sizeof R);
    int r = 0;
    for (int c = 23; c >= 0 && r < 12; c--) {
        int p = -1; for (int i = r; i < 12; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint32_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 12; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < 12; i++) { h ^= R[i]; h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}
static int maxscan = 24;
static void ext_search(uint32_t Olast) {
    if (dim == 12) {
        if (nsolstore < MAXSOLSTORE) memcpy(solbasis[nsolstore++], basis, sizeof(uint32_t) * 12);
        solhash += code_hash(basis);
        nsol++; return;
    }
    nodes[dim]++;
    uint32_t cb[2][969]; int cur = 0, best = 1 << 30; int scanned = 0;
    for (int t = 0; t < 70 && best > 0 && scanned < maxscan; t++) {
        uint32_t T = _pdep_u32(pat4[t], Olast);
        for (uint32_t r = FULL24 & ~Olast; r && best > 0 && scanned < maxscan; r &= r - 1) {
            uint32_t F = T | (r & -r);
            if (covered(F)) continue;
            scanned++;
            int c = cands(F, cb[cur], best);
            if (c < best) { best = c; cur ^= 1; }
        }
    }
    if (best == (1 << 30)) {
        for (uint32_t F = 0x1F; ; ) {
            if (!covered(F)) { best = cands(F, cb[cur], 1 << 30); cur ^= 1; break; }
            uint32_t t = F | (F - 1); F = (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctz(F) + 1));
            if (F >> 24) { fprintf(stderr, "no uncovered 5-set at dim %d\n", dim); exit(1); }
        }
    }
    if (best == 0) return;
    uint32_t list[969]; memcpy(list, cb[cur ^ 1], sizeof(uint32_t) * best);
    int nl = best;
    for (int i = 0; i < nl; i++) {
        uint32_t buf[2048];
        int m = addK(list[i], buf);
        ext_search(list[i]);
        undoK(buf, m);
    }
}

/* ---- forbidden sets from a Hermitian self-dual [24,12,8] code ---- */
typedef struct { uint32_t *s8, *s10, *s12; int n8, n10, n12; } supp_t;
static void supp_cb(f4v w, int nrows, void *c) {
    supp_t *S = (supp_t *)c; int wt = f4wt(w); uint32_t s = f4supp(w);
    if (wt == 8) S->s8[S->n8++] = s; else if (wt == 10) S->s10[S->n10++] = s; else if (wt == 12) S->s12[S->n12++] = s;
}
static int cmpu32(const void *a, const void *b) { uint32_t x = *(uint32_t *)a, y = *(uint32_t *)b; return x < y ? -1 : x > y; }
static int uniq32(uint32_t *a, int n) { qsort(a, n, 4, cmpu32); int m = 0; for (int i = 0; i < n; i++) if (!m || a[m - 1] != a[i]) a[m++] = a[i]; return m; }
static uint32_t *E_s8, *E_s10, *E_s12; static int E_n8, E_n10, E_n12;
static long set_forbidden_from_E(const f4v *gen) {
    static uint32_t s8[200000], s10[400000], s12[800000];
    supp_t S = { s8, s10, s12, 0, 0, 0 };
    sd_lowwords(gen, 24, 12, supp_cb, &S);
    S.n8 = uniq32(s8, S.n8); S.n10 = uniq32(s10, S.n10); S.n12 = uniq32(s12, S.n12);
    memset(forb8, 0, F8BYTES); memset(forb12, 0, F12BYTES);
    for (int i = 0; i < S.n8; i++) {
        uint32_t s = s8[i]; SET8(s);
        for (uint32_t a = s; a; a &= a - 1) for (uint32_t b = FULL24 & ~s; b; b &= b - 1) SET8((s ^ (a & -a)) | (b & -b));
    }
    for (int i = 0; i < S.n10; i++) {
        uint32_t s = s10[i];
        for (uint32_t a = s; a; a &= a - 1) for (uint32_t b = a & (a - 1); b; b &= b - 1) SET8(s ^ (a & -a) ^ (b & -b));
    }
    for (int i = 0; i < S.n12; i++) SET12(s12[i]);
    long c = 0; for (int i = 0; i < F8BYTES; i++) c += __builtin_popcount(forb8[i]);
    E_s8 = s8; E_s10 = s10; E_s12 = s12; E_n8 = S.n8; E_n10 = S.n10; E_n12 = S.n12;
    return c;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint32_t applyperm(const int *p, uint32_t w) { uint32_t o = 0; for (; w; w &= w - 1) o |= 1u << p[__builtin_ctz(w)]; return o; }
static int parse_code_line(const char *line, f4v *gen) {
    if (strlen(line) < 192) return 0;
    for (int i = 0; i < 12; i++) {
        char t[9]; memcpy(t, line + 16 * i, 8); t[8] = 0; gen[i].a = strtoul(t, 0, 16);
        memcpy(t, line + 16 * i + 8, 8); gen[i].b = strtoul(t, 0, 16);
    }
    return 1;
}
#endif
