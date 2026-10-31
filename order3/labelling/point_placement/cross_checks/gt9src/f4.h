/* F4 = {0,1,w,w^2=1+w} vectors of length <= 32 as two bit planes: element at coordinate i is a_i + b_i w.
   Scalar codes: 0=(0,0) 1=(1,0) w=(0,1) w2=(1,1); as 2-bit ints e = a + 2b, so 0,1,2(=w),3(=w2).
   Hermitian form <x,y> = sum x_i conj(y_i), conj(w) = w2.  Bilinear dot x.y = sum x_i y_i.            */
#ifndef F4_H
#define F4_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { uint32_t a, b; } f4v;
static inline f4v f4add(f4v x, f4v y) { f4v r = { x.a ^ y.a, x.b ^ y.b }; return r; }
static inline f4v f4mw(f4v x) { f4v r = { x.b, x.a ^ x.b }; return r; }        /* times w  */
static inline f4v f4mw2(f4v x) { f4v r = { x.a ^ x.b, x.a }; return r; }       /* times w2 */
static inline f4v f4conj(f4v x) { f4v r = { x.a ^ x.b, x.b }; return r; }
static inline uint32_t f4supp(f4v x) { return x.a | x.b; }
static inline int f4wt(f4v x) { return __builtin_popcount(x.a | x.b); }
static inline int f4iszero(f4v x) { return (x.a | x.b) == 0; }
static inline int f4eq(f4v x, f4v y) { return x.a == y.a && x.b == y.b; }
/* scalar e in {0..3} times vector */
static inline f4v f4smul(int e, f4v x) {
    f4v z = { 0, 0 };
    switch (e) { case 0: return z; case 1: return x; case 2: return f4mw(x); default: return f4mw2(x); }
}
static inline int f4get(f4v x, int i) { return ((x.a >> i) & 1) | (((x.b >> i) & 1) << 1); }
static inline void f4set(f4v *x, int i, int e) {
    x->a = (x->a & ~(1u << i)) | ((uint32_t)(e & 1) << i);
    x->b = (x->b & ~(1u << i)) | ((uint32_t)((e >> 1) & 1) << i);
}
/* scalar arithmetic */
static const int F4MUL[4][4] = { {0,0,0,0}, {0,1,2,3}, {0,2,3,1}, {0,3,1,2} };
static const int F4INV[4] = { 0, 1, 3, 2 };
static const int F4CONJ[4] = { 0, 1, 3, 2 };
/* Hermitian inner product as scalar code */
static inline int f4herm(f4v x, f4v y) {
    int re = __builtin_parity((x.a & y.a) ^ (x.a & y.b) ^ (x.b & y.b));
    int im = __builtin_parity((x.a & y.b) ^ (x.b & y.a));
    return re | (im << 1);
}
/* bilinear dot product sum x_i y_i */
static inline int f4dot(f4v x, f4v y) { return f4herm(x, f4conj(y)); }

/* ---------- RNG: xoshiro256** ---------- */
typedef struct { uint64_t s[4]; } rng_t;
static inline uint64_t rotl64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t rng_next(rng_t *r) {
    uint64_t *s = r->s, res = rotl64(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl64(s[3], 45);
    return res;
}
static inline void rng_seed(rng_t *r, uint64_t seed) {
    for (int i = 0; i < 4; i++) {
        uint64_t z = (seed += 0x9e3779b97f4a7c15ULL);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        r->s[i] = z ^ (z >> 31);
    }
}

/* ---------- linear algebra ---------- */
/* Reduced row echelon form in place over F4; rows[0..k-1], length n.  Returns rank; piv[r] = pivot col of row r.
   Pivot entries are normalised to 1. Rows beyond rank are zero. Columns scanned in the order colorder (NULL =
   0..n-1). */
static int f4rref(f4v *rows, int k, int n, int *piv, const int *colorder) {
    int r = 0;
    for (int ci = 0; ci < n && r < k; ci++) {
        int c = colorder ? colorder[ci] : ci;
        int p = -1;
        for (int i = r; i < k; i++) if ((f4supp(rows[i]) >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        f4v t = rows[p]; rows[p] = rows[r]; rows[r] = t;
        rows[r] = f4smul(F4INV[f4get(rows[r], c)], rows[r]);
        for (int i = 0; i < k; i++) if (i != r) {
            int e = f4get(rows[i], c);
            if (e) rows[i] = f4add(rows[i], f4smul(e, rows[r]));
        }
        if (piv) piv[r] = c;
        r++;
    }
    return r;
}
/* null space of the bilinear form: all v with v.rows[i] = 0 for all i.  Output basis in out (returns dim). */
static int f4nullspace(const f4v *rows_in, int k, int n, f4v *out) {
    f4v rows[32]; int piv[32];
    memcpy(rows, rows_in, sizeof(f4v) * k);
    int r = f4rref(rows, k, n, piv, NULL);
    int ispiv[32] = { 0 };
    for (int i = 0; i < r; i++) ispiv[piv[i]] = 1;
    int d = 0;
    for (int c = 0; c < n; c++) if (!ispiv[c]) {
        /* free variable c = 1; pivot vars: x_piv[i] = -rows[i][c] = rows[i][c] (char 2) */
        f4v v = { 0, 0 };
        f4set(&v, c, 1);
        for (int i = 0; i < r; i++) { int e = f4get(rows[i], c); if (e) f4set(&v, piv[i], e); }
        out[d++] = v;
    }
    return d;
}
/* Hermitian dual basis: v with <v, rows[i]> = 0, i.e. v . conj(rows[i]) = 0 */
static int f4hermdual(const f4v *rows_in, int k, int n, f4v *out) {
    f4v c[32];
    for (int i = 0; i < k; i++) c[i] = f4conj(rows_in[i]);
    return f4nullspace(c, k, n, out);
}
static int f4rank(const f4v *rows_in, int k, int n) {
    f4v rows[64]; memcpy(rows, rows_in, sizeof(f4v) * k);
    return f4rref(rows, k, n, NULL, NULL);
}
static void f4print(FILE *f, f4v x, int n) {
    static const char ch[4] = { '0', '1', 'w', 'W' };
    for (int i = 0; i < n; i++) fputc(ch[f4get(x, i)], f);
}
static f4v f4parse(const char *s, int n) {
    f4v v = { 0, 0 };
    for (int i = 0; i < n; i++) {
        int e = s[i] == '0' ? 0 : s[i] == '1' ? 1 : (s[i] == 'w' || s[i] == '2') ? 2 : 3;
        f4set(&v, i, e);
    }
    return v;
}
#endif
