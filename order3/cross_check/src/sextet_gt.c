/* sextet_gt.c -- own ground truth: all labelled Golay codes containing the sextet {0-3},{4-7},...,{20-23}
   (BFS orbit of one such code under S4 wr S6), and random instances
     F8 = {8-sets not orthogonal to the sextet code} u R8,  F12 = R12   (R8, R12 random with given densities)
   usage: sextet_gt DENS8 DENS12 SEED OUTPREFIX   -> OUTPREFIX.f8, OUTPREFIX.f12 (raw 2^21-byte bitmaps) and
          prints the exact number of solutions and the sum of code_hash (c3class definition) over them.
   PLANTFRAC: none. */
#include "golay24.h"
#include <stdint.h>
static uint64_t code_hash_c3(const uint32_t *B) {
    uint32_t R[12]; memcpy(R, B, sizeof R); int r = 0;
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
/* canonical basis: RREF from bit 23 down (same as in code_hash) */
static void rref(uint32_t *R) {
    int r = 0;
    for (int c = 23; c >= 0 && r < 12; c--) {
        int p = -1; for (int i = r; i < 12; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint32_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 12; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
}
typedef struct { uint32_t b[12]; } code_t;
static code_t *tab; static uint8_t *used; static size_t tsz;
static uint64_t keyhash(const code_t *c) { uint64_t h = 0x12345; for (int i = 0; i < 12; i++) h = (h ^ c->b[i]) * 0x100000001b3ULL, h ^= h >> 31; return h; }
static int insert(const code_t *c) {
    size_t h = keyhash(c) & (tsz - 1);
    while (used[h]) { if (!memcmp(tab[h].b, c->b, sizeof c->b)) return 0; h = (h + 1) & (tsz - 1); }
    used[h] = 1; tab[h] = *c; return 1;
}
static uint64_t rs;
static double urand(void) { rs += 0x9e3779b97f4a7c15ULL; uint64_t z = rs; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; z ^= z >> 31; return (double)(z >> 11) * 0x1.0p-53; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    double d8 = atof(argv[1]), d12 = atof(argv[2]); rs = strtoull(argv[3], 0, 10) * 1000003ULL + 17;
    golay_build();
    /* find a sextet of the reference code: the 5 octads through {p0..p3} of OCT[0] */
    uint32_t T0 = 0; int n = 0; for (uint32_t t = OCT[0]; t && n < 4; t &= t - 1, n++) T0 |= t & -t;
    uint32_t tet[6]; int nt = 0; tet[nt++] = T0;
    for (int k = 0; k < 759; k++) if ((OCT[k] & T0) == T0) tet[nt++] = OCT[k] & ~T0;
    if (nt != 6) { fprintf(stderr, "sextet construction failed %d\n", nt); return 2; }
    uint32_t all = 0; for (int i = 0; i < 6; i++) { if (__builtin_popcount(tet[i]) != 4 || (all & tet[i])) { fprintf(stderr, "bad tetrad\n"); return 2; } all |= tet[i]; }
    int pm[24], k = 0; for (int i = 0; i < 6; i++) for (uint32_t t = tet[i]; t; t &= t - 1) pm[__builtin_ctz(t)] = k++;
    code_t c0; for (int i = 0; i < 12; i++) c0.b[i] = perm_apply(pm, GB[i]); rref(c0.b);
    /* generators of S4 wr S6 */
    int g[4][24];
    for (int i = 0; i < 24; i++) { g[0][i] = g[1][i] = g[2][i] = g[3][i] = i; }
    g[0][0] = 1; g[0][1] = 0;                                   /* (0 1) */
    g[1][0] = 1; g[1][1] = 2; g[1][2] = 3; g[1][3] = 0;         /* (0 1 2 3) */
    for (int j = 0; j < 4; j++) { g[2][j] = 4 + j; g[2][4 + j] = j; }        /* swap tetrads 0,1 */
    for (int i = 0; i < 24; i++) g[3][i] = (i + 4) % 24;                     /* cycle tetrads */
    tsz = 1 << 22; tab = malloc(sizeof(code_t) * tsz); used = calloc(tsz, 1);
    code_t *q = malloc(sizeof(code_t) * 1100000); size_t qh = 0, qt = 0;
    insert(&c0); q[qt++] = c0;
    while (qh < qt) {
        code_t c = q[qh++];
        for (int gi = 0; gi < 4; gi++) { code_t d; for (int i = 0; i < 12; i++) d.b[i] = perm_apply(g[gi], c.b[i]); rref(d.b); if (insert(&d)) { if (qt >= 1100000) { fprintf(stderr, "queue overflow\n"); return 3; } q[qt++] = d; } }
    }
    fprintf(stderr, "orbit size %zu (expected 995328)\n", qt);
    /* instance */
    uint8_t *F8 = calloc(1u << 21, 1), *F12 = calloc(1u << 21, 1);
    uint32_t sx[6]; for (int i = 0; i < 6; i++) sx[i] = 0xfu << (4 * i);
    long long nf8 = 0, nf12 = 0;
    for (uint32_t s = 0; s < (1u << 24); s++) {
        int c = __builtin_popcount(s);
        if (c == 8) {
            int par = __builtin_popcount(s & sx[0]) & 1, bad = 0;
            for (int i = 1; i < 6; i++) if ((__builtin_popcount(s & sx[i]) & 1) != par) bad = 1;
            if (bad || urand() < d8) { F8[s >> 3] |= (uint8_t)(1u << (s & 7)); nf8++; }
        } else if (c == 12 && d12 > 0 && urand() < d12) { F12[s >> 3] |= (uint8_t)(1u << (s & 7)); nf12++; }
    }
    /* ground truth */
    long long nsol = 0; uint64_t hs = 0;
    for (size_t i = 0; i < qt; i++) {
        uint32_t *B = q[i].b, W[4096];
        for (int m = 0; m < 4096; m++) { uint32_t w = 0; for (int j = 0; j < 12; j++) if ((m >> j) & 1) w ^= B[j]; W[m] = w; }
        int ok = 1;
        for (int m = 1; m < 4096 && ok; m++) { int c = __builtin_popcount(W[m]); if (c == 8 && ((F8[W[m] >> 3] >> (W[m] & 7)) & 1)) ok = 0; if (c == 12 && ((F12[W[m] >> 3] >> (W[m] & 7)) & 1)) ok = 0; }
        if (ok) { nsol++; hs += code_hash_c3(B); }
    }
    char fn[4096];
    snprintf(fn, sizeof fn, "%s.f8", argv[4]); FILE *f = fopen(fn, "wb"); fwrite(F8, 1, 1u << 21, f); fclose(f);
    snprintf(fn, sizeof fn, "%s.f12", argv[4]); f = fopen(fn, "wb"); fwrite(F12, 1, 1u << 21, f); fclose(f);
    printf("GT d8=%g d12=%g seed=%s nsol=%lld hash=%016llx f8=%lld f12=%lld orbit=%zu\n", d8, d12, argv[3], nsol, (unsigned long long)hs, nf8, nf12, qt);
    return 0;
}
