/* codeinfo.h -- per-code analysis for the C3 audit (independent code).
   For a Hermitian self-dual [24,12] code given by 12 generator rows:
   - checks Hermitian self-orthogonality and rank 12,
   - enumerates all words of weight <= 8 (two complementary information sets; every word of weight <= 8 has
     <= 4 nonzero coordinates on one of them) -> d >= 8 check, projective weight-8 words (one per support),
   - rank of the weight-8 words,
   - support-only colour refinement (invariant under monomial maps, conjugation and permutations):
     code invariant hash, discreteness of the coordinate colouring, connectivity of the support hypergraph,
   - if discrete and connected: |Aut_Mon| = 3 is certified, and self-conjugacy is decided exactly (diagonal maps). */
#ifndef CODEINFO_H
#define CODEINFO_H
#include "f4a.h"

#define MAXW8 4096
typedef struct {
    int ok_so, rank, dmin_ok;      /* self-orthogonal, rank, no nonzero word of weight < 8 */
    int nw8;                        /* projective weight-8 words (= A8/3) */
    v24 w8[MAXW8];
    uint32_t s8[MAXW8];
    int rank8;                      /* rank of the weight-8 words */
    int ncolors, connected, covers;
    uint64_t inv;                   /* code invariant (supports only) */
    uint64_t col[24];
    int aut3_cert;                  /* 1: |Aut_Mon| = 3 certified */
    int selfconj;                   /* -1 unknown, 0/1 decided */
    v24 g[12]; int piv[12];         /* systematic generator on information set I */
} codeinfo;

static int ci_add_w8(codeinfo *ci, v24 x) {
    if (ci->nw8 >= MAXW8) return -1;
    ci->w8[ci->nw8] = x; ci->s8[ci->nw8] = vsupp(x); ci->nw8++; return 0;
}

/* DFS over combinations of <= 4 systematic rows with scalars (first chosen row scalar 1: projective) */
static void ci_dfs(codeinfo *ci, const v24 *g, int depth, int start, v24 cur, uint32_t Imask, int jside, int *bad) {
    for (int t = start; t < 12; t++) {
        for (int s = 1; s <= 3; s++) {
            if (depth == 0 && s != 1) break;
            v24 nw = vadd(cur, vscal(g[t], s));
            int w = vwt(nw);
            int keep = 1;
            if (jside) keep = (__builtin_popcount(vsupp(nw) & Imask) >= 5);
            if (keep) {
                if (w < 8) *bad = 1;
                else if (w == 8) { if (ci_add_w8(ci, nw) < 0) *bad = 2; }
            }
            if (depth + 1 < 4) ci_dfs(ci, g, depth + 1, t + 1, nw, Imask, jside, bad);
        }
    }
}

static int ci_rank_vectors(const v24 *x, int n) {
    v24 r[24]; int rank = 0;
    int cols[24]; for (int i = 0; i < 24; i++) cols[i] = i;
    for (int j = 0; j < n && rank < 12; j++) {
        v24 y = x[j];
        /* reduce y by current basis r[0..rank-1] (each with pivot pv) */
        static __thread int pv[24];
        for (int t = 0; t < rank; t++) { int s = vget(y, pv[t]); if (s) y = vadd(y, vscal(r[t], s)); }
        if (viszero(y)) continue;
        int c = __builtin_ctz(vsupp(y));
        y = vscal(y, F4INV[vget(y, c)]);
        for (int t = 0; t < rank; t++) { int s = vget(r[t], c); if (s) r[t] = vadd(r[t], vscal(y, s)); }
        r[rank] = y; pv[rank] = c; rank++;
    }
    (void)cols;
    return rank;
}

static int uf_find(int *p, int x) { while (p[x] != x) { p[x] = p[p[x]]; x = p[x]; } return x; }

/* returns 0 on success (code analysed), <0 on hard error */
static int codeinfo_analyse(codeinfo *ci, const v24 *rows) {
    memset(ci, 0, offsetof(codeinfo, w8));
    ci->nw8 = 0; ci->selfconj = -1;
    /* self-orthogonality */
    ci->ok_so = 1;
    for (int i = 0; i < 12; i++) for (int j = i; j < 12; j++) if (vherm(rows[i], rows[j])) ci->ok_so = 0;
    /* systematic form on I (natural column order) */
    v24 g[12]; memcpy(g, rows, sizeof g);
    int order[24]; for (int i = 0; i < 24; i++) order[i] = i;
    int piv[12];
    ci->rank = f4_rref(g, 12, order, 24, piv);
    if (ci->rank < 12) return 0;
    memcpy(ci->g, g, sizeof g); memcpy(ci->piv, piv, sizeof piv);
    uint32_t Imask = 0; for (int t = 0; t < 12; t++) Imask |= 1u << piv[t];
    /* systematic form on J = complement */
    v24 h[12]; memcpy(h, g, sizeof h);
    int jorder[24], nj = 0; for (int i = 0; i < 24; i++) if (!((Imask >> i) & 1)) jorder[nj++] = i;
    int pivJ[12];
    int rJ = f4_rref(h, 12, jorder, nj, pivJ);
    if (rJ < 12) { ci->dmin_ok = -1; return 0; }  /* cannot happen for a self-dual code */
    int bad = 0; v24 zero = { 0, 0 };
    ci_dfs(ci, g, 0, 0, zero, Imask, 0, &bad);
    ci_dfs(ci, h, 0, 0, zero, Imask, 1, &bad);
    ci->dmin_ok = (bad == 0);
    if (bad == 2) return -2;
    ci->rank8 = ci_rank_vectors(ci->w8, ci->nw8);
    /* support hypergraph connectivity and coverage */
    int p[24]; for (int i = 0; i < 24; i++) p[i] = i;
    uint32_t cov = 0;
    for (int j = 0; j < ci->nw8; j++) {
        uint32_t s = ci->s8[j]; cov |= s;
        int f = __builtin_ctz(s);
        for (uint32_t t = s & (s - 1); t; t &= t - 1) { int x = uf_find(p, f), y = uf_find(p, __builtin_ctz(t)); if (x != y) p[x] = y; }
    }
    ci->covers = (cov == 0xffffffu);
    int roots = 0; for (int i = 0; i < 24; i++) if (uf_find(p, i) == i) roots++;
    ci->connected = (roots == 1);
    /* colour refinement on supports */
    int m = ci->nw8;
    static __thread uint16_t hist[MAXW8][9];
    static __thread uint64_t pc[MAXW8], pc2[MAXW8];
    memset(hist, 0, sizeof(uint16_t) * 9 * (size_t)m);
    for (int j = 0; j < m; j++) for (int k = j + 1; k < m; k++) {
        int x = __builtin_popcount(ci->s8[j] & ci->s8[k]);
        hist[j][x]++; hist[k][x]++;
    }
    int N[24][24]; memset(N, 0, sizeof N);
    for (int j = 0; j < m; j++) {
        uint32_t s = ci->s8[j];
        for (uint32_t t = s; t; t &= t - 1) { int x = __builtin_ctz(t); for (uint32_t u = t & (t - 1); u; u &= u - 1) { int y = __builtin_ctz(u); N[x][y]++; N[y][x]++; } }
    }
    for (int j = 0; j < m; j++) { uint64_t hsh = 0x1234567ULL; for (int x = 0; x < 9; x++) hsh = smix(hsh ^ ((uint64_t)hist[j][x] << 8 | (uint64_t)x)); pc[j] = hsh; }
    uint64_t c1[24], c2[24], c3[24], c4[24];
    for (int i = 0; i < 24; i++) c1[i] = 0;
    for (int j = 0; j < m; j++) { uint64_t f = smix(pc[j] ^ 0xa1ULL); for (uint32_t t = ci->s8[j]; t; t &= t - 1) c1[__builtin_ctz(t)] += f; }
    for (int i = 0; i < 24; i++) c1[i] = smix(c1[i] ^ 0xb2ULL);
    for (int i = 0; i < 24; i++) { uint64_t acc = 0; for (int k = 0; k < 24; k++) if (k != i) acc += smix(c1[k] ^ ((uint64_t)N[i][k] * 0x9e37ULL) ^ 0xc3ULL); c2[i] = smix(c1[i] ^ smix(acc)); }
    for (int j = 0; j < m; j++) { uint64_t acc = 0; for (uint32_t t = ci->s8[j]; t; t &= t - 1) acc += smix(c2[__builtin_ctz(t)] ^ 0xd4ULL); pc2[j] = smix(pc[j] ^ smix(acc)); }
    for (int i = 0; i < 24; i++) c3[i] = 0;
    for (int j = 0; j < m; j++) { uint64_t f = smix(pc2[j] ^ 0xe5ULL); for (uint32_t t = ci->s8[j]; t; t &= t - 1) c3[__builtin_ctz(t)] += f; }
    for (int i = 0; i < 24; i++) c3[i] = smix(c2[i] ^ smix(c3[i]));
    for (int i = 0; i < 24; i++) { uint64_t acc = 0; for (int k = 0; k < 24; k++) if (k != i) acc += smix(c3[k] ^ ((uint64_t)N[i][k] * 0x7f4aULL) ^ 0xf6ULL); c4[i] = smix(c3[i] ^ smix(acc)); }
    int nc = 0;
    for (int i = 0; i < 24; i++) { int dup = 0; for (int k = 0; k < i; k++) if (c4[k] == c4[i]) { dup = 1; break; } if (!dup) nc++; }
    ci->ncolors = nc;
    memcpy(ci->col, c4, sizeof c4);
    uint64_t sc = 0, ss = 0;
    for (int i = 0; i < 24; i++) sc += smix(c4[i] ^ 0x51ULL);
    for (int j = 0; j < m; j++) ss += smix(pc2[j] ^ 0x62ULL);
    ci->inv = smix(smix((uint64_t)m) ^ smix(sc) ^ smix(ss + 0x73ULL));
    /* certificates in the discrete connected case */
    ci->aut3_cert = 0; ci->selfconj = -1;
    if (nc == 24 && ci->connected && ci->covers) {
        ci->aut3_cert = 1;
        /* self-conjugacy: find diagonal D with D conj(w) = lambda_w w for all weight-8 w */
        int d[24]; for (int i = 0; i < 24; i++) d[i] = -1;
        static __thread int lam[MAXW8];
        for (int j = 0; j < m; j++) lam[j] = -1;
        d[0] = 0;
        int changed = 1, consistent = 1;
        while (changed && consistent) {
            changed = 0;
            for (int j = 0; j < m && consistent; j++) {
                uint32_t s = ci->s8[j];
                if (lam[j] < 0) {
                    for (uint32_t t = s; t; t &= t - 1) { int i = __builtin_ctz(t); if (d[i] >= 0) { lam[j] = ((d[i] - 2 * F4LOG[vget(ci->w8[j], i)]) % 3 + 3) % 3; changed = 1; break; } }
                }
                if (lam[j] >= 0) {
                    for (uint32_t t = s; t; t &= t - 1) {
                        int i = __builtin_ctz(t);
                        int e = (lam[j] + 2 * F4LOG[vget(ci->w8[j], i)]) % 3;
                        if (d[i] < 0) { d[i] = e; changed = 1; }
                        else if (d[i] != e) { consistent = 0; break; }
                    }
                }
            }
        }
        for (int i = 0; i < 24; i++) if (d[i] < 0) consistent = 0;
        if (!consistent) ci->selfconj = 0;
        else {
            int all = 1;
            for (int t = 0; t < 12 && all; t++) {
                v24 x = vconj(ci->g[t]), y = { 0, 0 };
                for (int i = 0; i < 24; i++) {
                    int s = vget(x, i);
                    if (s) { int v = f4mul(s, F4EXP[d[i]]); if (v & 1) y.a |= 1u << i; if (v & 2) y.b |= 1u << i; }
                }
                if (!f4_member(ci->g, ci->piv, 12, y)) all = 0;
            }
            ci->selfconj = all;
        }
    }
    return 0;
}
#endif
