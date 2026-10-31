/* Helpers for checking known Hermitian self-dual [24,12,8] codes against the class list cls24:
   mu-circulant matrices over F4 (elements 0,1,2=w,3=W=w^2; addition = XOR), generator checks, minimum distance,
   class key (cform.h) and the monomial canonical form. */
#ifndef KNOWN_H
#define KNOWN_H
#include "cform.h"
#include "golay.h"

typedef struct { int e[12][12]; } mat12;
static inline int gfadd(int x, int y) { return x ^ y; }
static inline int gfmul(int x, int y) { return F4MUL[x][y]; }
static inline int gfconj(int x) { return F4CONJ[x]; }
/* n x n mu-circulant matrix with first row r: row k+1 = (mu r_{n-1}, r_0, ..., r_{n-2}) applied to row k */
static void mucirc(const int *r, int n, int mu, mat12 *A) {
    for (int c = 0; c < n; c++) A->e[0][c] = r[c];
    for (int k = 1; k < n; k++) {
        A->e[k][0] = gfmul(mu, A->e[k - 1][n - 1]);
        for (int c = 1; c < n; c++) A->e[k][c] = A->e[k - 1][c - 1];
    }
}
static void conjT(const mat12 *A, int n, mat12 *B) { for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) B->e[i][j] = gfconj(A->e[j][i]); }
/* generator [I_k | M] (k = 12, M 12 x 12) as f4v rows of length 24 */
static void gen_IM(const mat12 *M, f4v *gen) {
    for (int i = 0; i < 12; i++) {
        f4v v = { 0, 0 }; f4set(&v, i, 1);
        for (int j = 0; j < 12; j++) f4set(&v, 12 + j, M->e[i][j]);
        gen[i] = v;
    }
}
/* Hermitian self-orthogonal (all pairs incl. i = j) and rank 12 */
static int check_sd(const f4v *gen, int k) {
    for (int i = 0; i < k; i++) for (int j = i; j < k; j++) if (f4herm(gen[i], gen[j])) return 0;
    return f4rank(gen, k, 24) == 12;
}
typedef struct { int dmin; long nw8; } lowst_t;
static void lowcb(f4v w, int nr, void *c) { lowst_t *s = (lowst_t *)c; int t = f4wt(w); if (t && t < s->dmin) s->dmin = t; if (t == 8) s->nw8++; }
/* minimum distance (capped at 9 when no word of weight <= 8 exists) and number of weight-8 words */
static int dmin_a8(const f4v *gen, long *a8) {
    lowst_t s = { 99, 0 };
    sd_lowwords(gen, 24, 8, lowcb, &s);
    *a8 = s.nw8;
    return s.dmin > 8 ? 9 : s.dmin;
}
/* class key (Mon x conj), |Aut_Mon|, self-conjugacy, and the monomial canonical form of C itself */
static int keys(const f4v *gen, f4v *key, f4v *monform, double *aut, int *sc) {
    f4v c1[16], c2[16], g2[16]; double a1, a2;
    if (canon_code(gen, 12, 24, 8, c1, &a1)) return -1;
    for (int r = 0; r < 12; r++) g2[r] = f4conj(gen[r]);
    if (canon_code(g2, 12, 24, 8, c2, &a2)) return -1;
    int c = mat_cmp(c1, c2, 12);
    memcpy(key, c <= 0 ? c1 : c2, sizeof(f4v) * 12);
    memcpy(monform, c1, sizeof(f4v) * 12);
    *aut = a1; *sc = (c == 0);
    return 0;
}
static void hexkey(const f4v *key, char *out) { for (int r = 0; r < 12; r++) sprintf(out + 16 * r, "%08x%08x", key[r].a, key[r].b); }
#endif
