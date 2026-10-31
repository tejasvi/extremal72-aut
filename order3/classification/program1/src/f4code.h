/* Code-level routines over F4 (needs f4.h): random Hermitian self-dual codes, low-weight word enumeration via two
   complementary information sets (valid for self-dual codes: the complement of an information set is one). */
#ifndef F4CODE_H
#define F4CODE_H
#include "f4.h"

/* uniformly random Hermitian self-dual code of even length n: sequential uniform isotropic vectors */
static void random_sd(rng_t *R, int n, f4v *gen) {
    int k = 0;
    while (k < n / 2) {
        f4v W[32];
        int dw = f4hermdual(gen, k, n, W);
        for (;;) {
            f4v v = { 0, 0 };
            for (int i = 0; i < dw; i++) v = f4add(v, f4smul((int)(rng_next(R) & 3), W[i]));
            if (f4iszero(v) || (f4wt(v) & 1)) continue;          /* isotropic iff even weight */
            gen[k] = v;
            if (f4rank(gen, k + 1, n) == k + 1) break;
        }
        k++;
    }
}

/* enumerate combinations of <= t rows (with nonzero scalars) of rows[0..k-1]; call cb(word, nrows, ctx) */
typedef void (*wordcb)(f4v w, int nrows, void *ctx);
static void comb_rec(const f4v *rows, int k, int start, int left, int used, f4v acc, wordcb cb, void *ctx) {
    if (used) cb(acc, used, ctx);
    if (!left) return;
    for (int i = start; i < k; i++) {
        f4v r = rows[i];
        f4v r1 = r, r2 = f4mw(r), r3 = f4mw2(r);
        comb_rec(rows, k, i + 1, left - 1, used + 1, f4add(acc, r1), cb, ctx);
        comb_rec(rows, k, i + 1, left - 1, used + 1, f4add(acc, r2), cb, ctx);
        comb_rec(rows, k, i + 1, left - 1, used + 1, f4add(acc, r3), cb, ctx);
    }
}

/* low-weight words of a Hermitian self-dual [n,n/2] code: calls cb exactly once for every nonzero codeword of
   weight <= W (and possibly for some heavier words; cb must filter).  gen: n/2 independent rows. */
typedef struct { uint32_t info1; int t1; int W; wordcb user; void *uctx; int pass; } lw_ctx;
static void lw_cb(f4v w, int nrows, void *c) {
    lw_ctx *L = (lw_ctx *)c;
    if (L->pass == 2 && __builtin_popcount(f4supp(w) & L->info1) <= L->t1) return;
    if (f4wt(w) <= L->W) L->user(w, nrows, L->uctx);
}
static void sd_lowwords(const f4v *gen, int n, int W, wordcb user, void *uctx) {
    int k = n / 2, piv[32], order[32];
    f4v G1[32], G2[32];
    memcpy(G1, gen, sizeof(f4v) * k);
    int r = f4rref(G1, k, n, piv, NULL);
    if (r != k) { fprintf(stderr, "sd_lowwords: rank %d != %d\n", r, k); exit(1); }
    uint32_t info1 = 0;
    for (int i = 0; i < k; i++) info1 |= 1u << piv[i];
    int m = 0;
    for (int c = 0; c < n; c++) if (!((info1 >> c) & 1)) order[m++] = c;
    for (int c = 0; c < n; c++) if ((info1 >> c) & 1) order[m++] = c;
    memcpy(G2, gen, sizeof(f4v) * k);
    r = f4rref(G2, k, n, piv, order);
    for (int i = 0; i < k; i++) if ((info1 >> piv[i]) & 1) { fprintf(stderr, "complement not info set\n"); exit(1); }
    int t1 = W / 2, t2 = W - t1 - 1;
    lw_ctx L = { info1, t1, W, user, uctx, 1 };
    f4v z = { 0, 0 };
    comb_rec(G1, k, 0, t1, 0, z, lw_cb, &L);
    L.pass = 2;
    comb_rec(G2, k, 0, t2, 0, z, lw_cb, &L);
}

/* full weight distribution by Gray code over the F2-basis {g_i, w g_i} (2k vectors) */
static void full_wd(const f4v *gen, int k, int n, uint64_t *A) {
    f4v B[64]; int m = 0;
    for (int i = 0; i < k; i++) { B[m++] = gen[i]; B[m++] = f4mw(gen[i]); }
    for (int i = 0; i <= n; i++) A[i] = 0;
    f4v cur = { 0, 0 };
    A[0]++;
    uint64_t N = 1ULL << m;
    for (uint64_t g = 1; g < N; g++) {
        int bit = __builtin_ctzll(g);
        cur = f4add(cur, B[bit]);
        A[f4wt(cur)]++;
    }
}
#endif
