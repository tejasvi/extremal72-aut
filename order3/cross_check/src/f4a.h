/* f4a.h -- independent bitsliced F4 utilities for the C3 audit (written from scratch for the audit).
   A vector of length <= 32 over F4 = {0,1,w,w^2}, w^2 = w + 1, is a pair of bit planes (a,b):
   coordinate i = a_i + b_i w.  Scalar codes: 0 = 0, 1 = 1, 2 = w, 3 = w^2 (= 1 + w). */
#ifndef F4A_H
#define F4A_H
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

typedef struct { uint32_t a, b; } v24;

static inline v24 vadd(v24 x, v24 y) { v24 r = { x.a ^ y.a, x.b ^ y.b }; return r; }
static inline v24 vmulw(v24 x) { v24 r = { x.b, x.a ^ x.b }; return r; }      /* times w   */
static inline v24 vmulw2(v24 x) { v24 r = { x.a ^ x.b, x.a }; return r; }     /* times w^2 */
static inline v24 vscal(v24 x, int s) {
    if (s == 1) return x;
    if (s == 2) return vmulw(x);
    if (s == 3) return vmulw2(x);
    v24 z = { 0, 0 }; return z;
}
static inline v24 vconj(v24 x) { v24 r = { x.a ^ x.b, x.b }; return r; }      /* x -> x^2 coordinatewise */
static inline uint32_t vsupp(v24 x) { return x.a | x.b; }
static inline int vwt(v24 x) { return __builtin_popcount(x.a | x.b); }
static inline int vget(v24 x, int i) { return (int)((x.a >> i) & 1u) | (int)(((x.b >> i) & 1u) << 1); }
static inline int viszero(v24 x) { return (x.a | x.b) == 0; }
static const int F4INV[4] = { 0, 1, 3, 2 };
static const int F4LOG[4] = { -1, 0, 1, 2 };
static const int F4EXP[3] = { 1, 2, 3 };
static inline int f4mul(int s, int t) { if (!s || !t) return 0; return F4EXP[(F4LOG[s] + F4LOG[t]) % 3]; }
/* product of two scalars written as planes: (a+bw)(c+dw) = (ac+bd) + (ad+bc+bd)w */
/* Hermitian form h(x,y) = sum_i x_i conj(y_i), returned as scalar code */
static inline int vherm(v24 x, v24 y) {
    v24 yc = vconj(y);
    uint32_t P = (x.a & yc.a) ^ (x.b & yc.b);
    uint32_t Q = (x.a & yc.b) ^ (x.b & yc.a) ^ (x.b & yc.b);
    return (__builtin_popcount(P) & 1) | ((__builtin_popcount(Q) & 1) << 1);
}

/* Gaussian elimination over F4 with a prescribed column order; returns rank. Rows are reduced in place to
   reduced row echelon form w.r.t. the columns visited; piv[r] = pivot column of row r (rows reordered). */
static int f4_rref(v24 *r, int k, const int *colorder, int ncols, int *piv) {
    int rank = 0;
    for (int ci = 0; ci < ncols && rank < k; ci++) {
        int c = colorder[ci], p = -1;
        for (int t = rank; t < k; t++) if (vget(r[t], c)) { p = t; break; }
        if (p < 0) continue;
        v24 tmp = r[p]; r[p] = r[rank]; r[rank] = tmp;
        r[rank] = vscal(r[rank], F4INV[vget(r[rank], c)]);
        for (int t = 0; t < k; t++) if (t != rank) {
            int s = vget(r[t], c);
            if (s) r[t] = vadd(r[t], vscal(r[rank], s));
        }
        piv[rank++] = c;
    }
    return rank;
}

/* membership in the code with systematic rows g[0..k-1] (g[t] has 1 at column piv[t], 0 at other pivots) */
static int f4_member(const v24 *g, const int *piv, int k, v24 x) {
    for (int t = 0; t < k; t++) { int s = vget(x, piv[t]); if (s) x = vadd(x, vscal(g[t], s)); }
    return viszero(x);
}

static int hexval(int ch) {
    if (ch >= '0' && ch <= '9') return ch - '0';
    if (ch >= 'a' && ch <= 'f') return ch - 'a' + 10;
    if (ch >= 'A' && ch <= 'F') return ch - 'A' + 10;
    return -1;
}
/* parse k rows in c3class layout B: per row 8 hex digits of the a plane then 8 hex digits of the b plane.
   returns pointer after the hex block, or NULL on error */
static const char *parse_rows_B(const char *s, v24 *r, int k) {
    for (int t = 0; t < k; t++) {
        uint32_t pl[2];
        for (int h = 0; h < 2; h++) {
            uint32_t v = 0;
            for (int q = 0; q < 8; q++) { int d = hexval((unsigned char)*s++); if (d < 0) return NULL; v = (v << 4) | (uint32_t)d; }
            pl[h] = v;
        }
        r[t].a = pl[0]; r[t].b = pl[1];
    }
    return s;
}

static inline uint64_t smix(uint64_t x) {   /* splitmix64 finaliser */
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}
#endif
