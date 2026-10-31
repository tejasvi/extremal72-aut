/* Canonical forms of F4-linear codes under monomial equivalence (and Mon x <conjugation>), via nauty.
   Graph: X(i,a) = 3i+a for coordinate i and a in Z/3 (meaning "omega^a in coordinate i"), directed 3-cycles
   X(i,a) -> X(i,a+1); one vertex Y(w) per word w of a monomially invariant spanning word set W (closed under
   scalars), joined (both directions) to X(i, log w_i) for w_i != 0.  Graph isomorphisms <-> monomial maps
   (the directed cycles force each triple to rotate, i.e. a scaling; Y vertices are words, so the map preserves
   span W = C).  Canonical code: coordinate i -> rank of its earliest X vertex in the canonical labelling,
   scaled by omega^{-a_i} (a_i = that vertex), then reduced row echelon form.  Compile with
   -DWORDSIZE=64 -DMAXN=0 -Inautybuild, link nautybuild/libnauty64.a. */
#ifndef CFORM_H
#define CFORM_H
#include "f4code.h"
#include "nauty.h"
#include "nausparse.h"
#include <math.h>

static const int F4LOG[4] = { -1, 0, 1, 2 };
static const int F4EXP[3] = { 1, 2, 3 };
typedef struct { f4v *w; int n, cap; } wlist_t;
static void wl_add(wlist_t *L, f4v x) {
    if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 1024; L->w = realloc(L->w, sizeof(f4v) * L->cap); }
    L->w[L->n++] = x;
}
/* enumerate all nonzero words of a code (k <= 12) by Gray code, calling cb */
static void all_words(const f4v *gen, int k, void (*cb)(f4v, void *), void *ctx) {
    f4v B[24]; int m = 0;
    for (int i = 0; i < k; i++) { B[m++] = gen[i]; B[m++] = f4mw(gen[i]); }
    f4v cur = { 0, 0 };
    for (uint64_t g = 1; g < (1ULL << m); g++) { cur = f4add(cur, B[__builtin_ctzll(g)]); cb(cur, ctx); }
}
typedef struct { wlist_t *L; int wmin, wmax; } wsel_t;
static void wsel_cb(f4v x, void *c) { wsel_t *s = (wsel_t *)c; int w = f4wt(x); if (w >= s->wmin && w <= s->wmax) wl_add(s->L, x); }
static void wsel_cb2(f4v x, int nr, void *c) { wsel_cb(x, c); }
/* words of weight in [wmin,wmax]: via two information sets for self-dual codes (n = 2k), else full enumeration */
static void select_words(const f4v *gen, int k, int n, int wmin, int wmax, wlist_t *L) {
    wsel_t s = { L, wmin, wmax };
    if (2 * k == n && k > 6) sd_lowwords(gen, n, wmax, wsel_cb2, &s);
    else all_words(gen, k, wsel_cb, &s);
}

/* canonical form.  W: spanning, monomially invariant word set (closed under scalars).  Output: canonical RREF
   (k rows) in canon[], |Aut_Mon| in *autsz (double).  Returns 0 on success. */
static int canon_from_words(const f4v *gen, int k, int n, const f4v *W, int nw, f4v *canon, double *autsz) {
    int nv = 3 * n + nw;
    size_t ne = 3 * n; for (int j = 0; j < nw; j++) ne += 2 * (size_t)f4wt(W[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "canon");
    sg.nv = nv; sg.nde = ne;
    /* degrees */
    int *deg = calloc(nv, sizeof(int));
    for (int i = 0; i < 3 * n; i++) deg[i] = 1;
    for (int j = 0; j < nw; j++) { uint32_t s = f4supp(W[j]); deg[3 * n + j] = __builtin_popcount(s); for (; s; s &= s - 1) { int i = __builtin_ctz(s); deg[3 * i + F4LOG[f4get(W[j], i)]]++; } }
    size_t pos = 0;
    for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int a = 0; a < 3; a++) { int v = 3 * i + a; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + (a + 1) % 3; }
    for (int j = 0; j < nw; j++) {
        int y = 3 * n + j;
        for (uint32_t s = f4supp(W[j]); s; s &= s - 1) {
            int i = __builtin_ctz(s), x = 3 * i + F4LOG[f4get(W[j], i)];
            sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y;
        }
    }
    free(deg);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    for (int v = 0; v < nv; v++) { lab[v] = v; ptn[v] = 1; }
    ptn[3 * n - 1] = 0; ptn[nv - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt);
    opt.getcanon = TRUE; opt.defaultptn = FALSE;
    statsblk st;
    SG_DECL(cg);
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, &cg);
    *autsz = st.grpsize1 * pow(10.0, st.grpsize2);
    int *posv = malloc(sizeof(int) * nv);
    for (int p = 0; p < nv; p++) posv[lab[p]] = p;
    int first[32], ai[32], order[32];
    for (int i = 0; i < n; i++) {
        int best = 1 << 30, ba = 0;
        for (int a = 0; a < 3; a++) if (posv[3 * i + a] < best) { best = posv[3 * i + a]; ba = a; }
        first[i] = best; ai[i] = ba; order[i] = i;
    }
    for (int i = 1; i < n; i++) { int t = order[i], j = i; while (j > 0 && first[order[j - 1]] > first[t]) { order[j] = order[j - 1]; j--; } order[j] = t; }
    int newpos[32]; for (int p = 0; p < n; p++) newpos[order[p]] = p;
    for (int r = 0; r < k; r++) {
        f4v x = { 0, 0 };
        for (int i = 0; i < n; i++) {
            int e = f4get(gen[r], i);
            if (e) f4set(&x, newpos[i], F4MUL[e][F4EXP[(3 - ai[i]) % 3]]);
        }
        canon[r] = x;
    }
    int piv[32];
    int rk = f4rref(canon, k, n, piv, NULL);
    free(posv); free(lab); free(ptn); free(orb);
    SG_FREE(sg); SG_FREE(cg);
    return rk == k ? 0 : -1;
}
/* word set: all words of weight in [wmin, w] for the smallest w >= wmin making them span (all words if k <= 6) */
static int canon_code(const f4v *gen, int k, int n, int wmin, f4v *canon, double *autsz) {
    wlist_t L = { 0, 0, 0 };
    if (k <= 6) { wsel_t s = { &L, 1, n }; all_words(gen, k, wsel_cb, &s); }
    else {
        int wmax = wmin;
        for (;;) {
            L.n = 0; select_words(gen, k, n, wmin, wmax, &L);
            if (L.n && f4rank(L.w, L.n < 64 ? L.n : 64, n) == k) break;          /* quick check */
            /* full rank check */
            f4v R[64]; int r = 0;
            for (int j = 0; j < L.n && r < k; j++) { R[r] = L.w[j]; if (f4rank(R, r + 1, n) == r + 1) r++; }
            if (r == k) break;
            wmax += 2; if (wmax > n) { free(L.w); return -1; }
        }
    }
    int ret = canon_from_words(gen, k, n, L.w, L.n, canon, autsz);
    free(L.w);
    return ret;
}
static uint64_t mat_hash(const f4v *M, int k) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (int r = 0; r < k; r++) { h ^= M[r].a; h *= 0x100000001b3ULL; h ^= M[r].b; h *= 0x100000001b3ULL; h ^= h >> 31; }
    return h;
}
static int mat_cmp(const f4v *A, const f4v *B, int k) {
    for (int r = 0; r < k; r++) { if (A[r].a != B[r].a) return A[r].a < B[r].a ? -1 : 1; if (A[r].b != B[r].b) return A[r].b < B[r].b ? -1 : 1; }
    return 0;
}
/* class key under Mon x <conj>: min of canonical forms of C and conj(C); *selfconj = 1 if equal */
static int canon_class(const f4v *gen, int k, int n, int wmin, f4v *key, double *autsz, int *selfconj) {
    f4v c1[16], c2[16], g2[16]; double a1, a2;
    if (canon_code(gen, k, n, wmin, c1, &a1)) return -1;
    for (int r = 0; r < k; r++) g2[r] = f4conj(gen[r]);
    if (canon_code(g2, k, n, wmin, c2, &a2)) return -1;
    int c = mat_cmp(c1, c2, k);
    memcpy(key, c <= 0 ? c1 : c2, sizeof(f4v) * k);
    *autsz = a1; *selfconj = (c == 0);
    return 0;
}
#endif
