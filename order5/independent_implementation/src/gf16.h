/* gf16.h -- GF(16) = GF(2)[x]/(x^4+x^3+x^2+x+1), Hermitian form, weights, Fano side function M.
 * Written independently from SPEC.md.  Vectors of GF(16)^7 are packed in a uint32_t,
 * coordinate i in bits 4i..4i+3.  All tables are computed at start-up by gf_init(). */
#ifndef GF16_H
#define GF16_H
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GF_MOD 0x1F                      /* x^4+x^3+x^2+x+1 */
static uint8_t MUL[16][16], INV[16], CONJ[16], NRM[16], NCLS[16], WTE[16], SQR[16];
/* NCLS (norm class): 0 = zero, 1 = norm 1, 2 = norm GF4_W, 3 = norm GF4_W2 */
static int GF4_W, GF4_W2;
static const int CLSWT[4] = {0, 4, 2, 2};
static int CLS_REP[4];
static uint8_t NP_LO[65536];             /* coords 0..3 -> class pattern bits 0..7 */
static uint8_t NP_HI[4096];              /* coords 4..6 -> class pattern bits 8..13 */
static uint8_t MTAB[16384];              /* M as a function of the class pattern */
static uint8_t SM[16][256];              /* c * (pair of coordinates) */
static uint8_t H2[256][256];             /* u0 conj(v0) + u1 conj(v1) for byte-packed pairs */
static uint8_t SQ2[256];                 /* Frobenius on a byte (two coordinates) */
static const int LINES[7][3] = {{0,1,3},{1,2,4},{2,3,5},{3,4,6},{4,5,0},{5,6,1},{6,0,2}};
static int PS_MASK[16], PS_X[16];        /* the 16 pairs (S,x) of the spec, S as a bitmask */
static int AUT[168][7];                  /* Fano automorphisms (point maps i -> AUT[g][i]) */
static int NAUT = 0;

static int gf_mul_slow(int a, int b) {
    int r = 0;
    for (int k = 0; k < 4; k++) if ((b >> k) & 1) r ^= a << k;
    for (int k = 7; k >= 4; k--) if ((r >> k) & 1) r ^= GF_MOD << (k - 4);
    return r;
}
static int gf_pow(int a, int e) { int r = 1; while (e--) r = MUL[r][a]; return r; }

/* M from a weight vector, literally as in the spec */
static int M_weights(const int w[7]) {
    int best = 1 << 30;
    for (int t = 0; t < 16; t++) {
        int S = PS_MASK[t], val = PS_X[t];
        for (int i = 0; i < 7; i++) {
            if ((S >> i) & 1) val += 5 - w[i]; else val += w[i];
        }
        if (val < best) best = val;
    }
    return best;
}

static void gf_init(void) {
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) MUL[a][b] = gf_mul_slow(a, b);
    for (int a = 0; a < 16; a++) {
        CONJ[a] = gf_pow(a, 4); NRM[a] = gf_pow(a, 5); SQR[a] = MUL[a][a];
        INV[a] = 0;
        for (int b = 1; b < 16; b++) if (MUL[a][b] == 1) INV[a] = b;
    }
    /* GF(4) = image of the norm; pick w as the smaller of the two non-trivial elements */
    GF4_W = -1; GF4_W2 = -1;
    for (int a = 2; a < 16; a++) {
        int isnorm = 0;
        for (int b = 0; b < 16; b++) if (NRM[b] == a) isnorm = 1;
        if (isnorm) { if (GF4_W < 0) GF4_W = a; else GF4_W2 = a; }
    }
    for (int a = 0; a < 16; a++) {
        if (a == 0) NCLS[a] = 0;
        else if (NRM[a] == 1) NCLS[a] = 1;
        else if (NRM[a] == GF4_W) NCLS[a] = 2;
        else if (NRM[a] == GF4_W2) NCLS[a] = 3;
        else { fprintf(stderr, "norm outside GF4\n"); exit(1); }
        WTE[a] = CLSWT[NCLS[a]];
    }
    for (int c = 0; c < 4; c++) { CLS_REP[c] = -1; for (int a = 15; a >= 0; a--) if (NCLS[a] == c) CLS_REP[c] = a; }
    /* pairs (S,x) */
    int t = 0;
    PS_MASK[t] = 0; PS_X[t] = 0; t++;
    for (int l = 0; l < 7; l++) { int m = 0; for (int k = 0; k < 3; k++) m |= 1 << LINES[l][k]; PS_MASK[t] = m; PS_X[t] = 1; t++; }
    for (int l = 0; l < 7; l++) { int m = 0; for (int k = 0; k < 3; k++) m |= 1 << LINES[l][k]; PS_MASK[t] = 0x7F & ~m; PS_X[t] = 0; t++; }
    PS_MASK[t] = 0x7F; PS_X[t] = 1; t++;
    /* class-pattern tables */
    for (int v = 0; v < 65536; v++) { int p = 0; for (int i = 0; i < 4; i++) p |= NCLS[(v >> (4*i)) & 15] << (2*i); NP_LO[v] = p; }
    for (int v = 0; v < 4096; v++) { int p = 0; for (int i = 0; i < 3; i++) p |= NCLS[(v >> (4*i)) & 15] << (2*i); NP_HI[v] = p; }
    for (int p = 0; p < 16384; p++) { int w[7]; for (int i = 0; i < 7; i++) w[i] = CLSWT[(p >> (2*i)) & 3]; MTAB[p] = M_weights(w); }
    for (int c = 0; c < 16; c++) for (int b = 0; b < 256; b++) SM[c][b] = MUL[c][b & 15] | (MUL[c][b >> 4] << 4);
    for (int x = 0; x < 256; x++) for (int y = 0; y < 256; y++) H2[x][y] = MUL[x & 15][CONJ[y & 15]] ^ MUL[x >> 4][CONJ[y >> 4]];
    for (int b = 0; b < 256; b++) SQ2[b] = SQR[b & 15] | (SQR[b >> 4] << 4);
    /* Fano automorphisms: permutations mapping every line to a line */
    int perm[7] = {0,1,2,3,4,5,6};
    int linemask[7];
    for (int l = 0; l < 7; l++) { linemask[l] = 0; for (int k = 0; k < 3; k++) linemask[l] |= 1 << LINES[l][k]; }
    /* iterate permutations (Heap's algorithm would do; use simple lexicographic next_permutation) */
    for (;;) {
        int ok = 1;
        for (int l = 0; l < 7 && ok; l++) {
            int m = 0; for (int k = 0; k < 3; k++) m |= 1 << perm[LINES[l][k]];
            int found = 0; for (int l2 = 0; l2 < 7; l2++) if (linemask[l2] == m) found = 1;
            ok = found;
        }
        if (ok) { if (NAUT >= 168) { fprintf(stderr, "too many automorphisms\n"); exit(1); } memcpy(AUT[NAUT++], perm, sizeof perm); }
        int i = 5; while (i >= 0 && perm[i] > perm[i+1]) i--;
        if (i < 0) break;
        int j = 6; while (perm[j] < perm[i]) j--;
        int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        for (int a = i + 1, b = 6; a < b; a++, b--) { tmp = perm[a]; perm[a] = perm[b]; perm[b] = tmp; }
    }
    if (NAUT != 168) { fprintf(stderr, "NAUT=%d\n", NAUT); exit(1); }
}

static inline int vget(uint32_t v, int i) { return (v >> (4*i)) & 15; }
static inline uint32_t vset(uint32_t v, int i, int c) { return (v & ~(15u << (4*i))) | ((uint32_t)c << (4*i)); }
static inline int npat(uint32_t v) { return NP_LO[v & 0xFFFF] | (NP_HI[v >> 16] << 8); }
static inline int Mvec(uint32_t v) { return MTAB[npat(v)]; }
static inline uint32_t smul(int c, uint32_t v) {
    return (uint32_t)SM[c][v & 255] | ((uint32_t)SM[c][(v >> 8) & 255] << 8) |
           ((uint32_t)SM[c][(v >> 16) & 255] << 16) | ((uint32_t)SM[c][(v >> 24) & 255] << 24);
}
static inline int herm(uint32_t u, uint32_t v) {
    return H2[u & 255][v & 255] ^ H2[(u >> 8) & 255][(v >> 8) & 255] ^
           H2[(u >> 16) & 255][(v >> 16) & 255] ^ H2[(u >> 24) & 255][(v >> 24) & 255];
}
static inline uint32_t frob(uint32_t v) {
    return (uint32_t)SQ2[v & 255] | ((uint32_t)SQ2[(v >> 8) & 255] << 8) |
           ((uint32_t)SQ2[(v >> 16) & 255] << 16) | ((uint32_t)SQ2[(v >> 24) & 255] << 24);
}
/* coordinate permutation: result has coordinate g[i] equal to v_i */
static inline uint32_t vperm(uint32_t v, const int g[7]) {
    uint32_t w = 0;
    for (int i = 0; i < 7; i++) w |= (uint32_t)vget(v, i) << (4 * g[i]);
    return w;
}
/* class pattern permutation, same convention */
static inline int pperm(int p, const int g[7]) {
    int q = 0;
    for (int i = 0; i < 7; i++) q |= ((p >> (2*i)) & 3) << (2 * g[i]);
    return q;
}
/* Frobenius on class patterns: swaps classes 2 and 3 */
static inline int pfrob(int p) {
    int q = 0;
    for (int i = 0; i < 7; i++) { int c = (p >> (2*i)) & 3; if (c >= 2) c ^= 1; q |= c << (2*i); }
    return q;
}
/* class pattern of c*v given class pattern of v and class of c (c != 0) */
static inline int pscale(int p, int cc) {
    /* norms multiply in GF(4)^* = {1, w, w^2} = classes {1,2,3}; exponents 0,1,2 */
    static const int e_of[4] = {-1, 0, 1, 2}, c_of[3] = {1, 2, 3};
    int q = 0;
    for (int i = 0; i < 7; i++) { int c = (p >> (2*i)) & 3; if (c) c = c_of[(e_of[c] + e_of[cc]) % 3]; q |= c << (2*i); }
    return q;
}
/* sum of norms of a class pattern: returns the GF(16) element (it lies in GF(4)); <u,u> = psumnorm(npat(u)) */
static inline int psumnorm(int p) {
    int val_of[4] = {0, 1, GF4_W, GF4_W2};
    int s = 0;
    for (int i = 0; i < 7; i++) s ^= val_of[(p >> (2*i)) & 3];
    return s;
}
static inline int pnnz(int p) { int n = 0; for (int i = 0; i < 7; i++) if ((p >> (2*i)) & 3) n++; return n; }
/* minimal packed representative of the mu5-orbit of v (v != 0) */
static uint8_t MU5[5];
static void mu5_init(void) { int k = 0; for (int a = 1; a < 16; a++) if (NRM[a] == 1) MU5[k++] = a; }
static inline uint32_t minrep(uint32_t v) {
    uint32_t best = v;
    for (int k = 0; k < 5; k++) { uint32_t w = smul(MU5[k], v); if (w < best) best = w; }
    return best;
}
#endif
