/* red72.c -- numerical check of the reduction (C3 audit, independent code).
   For a code E (cls24 line) and a random labelled Golay code on E's coordinates, build the binary code
   C = {tripled Golay words} + psi(E) of length 72 (cycle i = coordinates 3i,3i+1,3i+2; psi(1)=110, psi(w)=011,
   psi(w^2)=101, so the cyclic shift inside each cycle is multiplication by w), check that C is self-dual and
   doubly even and that sigma (shift in every cycle) maps C to C, count ALL words of weight 4, 8, 12 directly
   (two complementary information sets, <= 6 rows each), and compare with
   (a) the formula count #{(g,e): 3|g| + 2wt(e) - 4|g & supp e| = w}, and
   (b) 3 x the (W8)/(W10)/(W12) violation counts.
   usage: red72 CODEFILE LINE SEED */
#include "golay24.h"
#include "f4a.h"
typedef struct { uint64_t lo; uint8_t hi; } b72;      /* bits 0..63 in lo, 64..71 in hi */
static inline void bset(b72 *x, int i) { if (i < 64) x->lo |= 1ULL << i; else x->hi |= (uint8_t)(1u << (i - 64)); }
static inline int bget(const b72 *x, int i) { return i < 64 ? (int)((x->lo >> i) & 1) : (x->hi >> (i - 64)) & 1; }
static inline b72 bxor(b72 a, b72 b) { b72 r = { a.lo ^ b.lo, (uint8_t)(a.hi ^ b.hi) }; return r; }
static inline int bwt(b72 a) { return __builtin_popcountll(a.lo) + __builtin_popcount(a.hi); }
static inline int bdot(b72 a, b72 b) { return (__builtin_popcountll(a.lo & b.lo) + __builtin_popcount(a.hi & b.hi)) & 1; }
static b72 psiE(v24 x) {
    b72 r = { 0, 0 };
    for (int i = 0; i < 24; i++) {
        int s = vget(x, i);
        if (s == 1) { bset(&r, 3 * i); bset(&r, 3 * i + 1); }          /* 110 */
        else if (s == 2) { bset(&r, 3 * i + 1); bset(&r, 3 * i + 2); }  /* 011 */
        else if (s == 3) { bset(&r, 3 * i); bset(&r, 3 * i + 2); }      /* 101 */
    }
    return r;
}
static b72 shift(b72 x) {   /* sigma: (b0,b1,b2) -> (b2,b0,b1) in every cycle */
    b72 r = { 0, 0 };
    for (int i = 0; i < 24; i++) { int b0 = bget(&x, 3 * i), b1 = bget(&x, 3 * i + 1), b2 = bget(&x, 3 * i + 2); if (b2) bset(&r, 3 * i); if (b0) bset(&r, 3 * i + 1); if (b1) bset(&r, 3 * i + 2); }
    return r;
}
static int rref72(b72 *R, int k, const int *colorder, int *piv) {
    int r = 0;
    for (int ci = 0; ci < 72 && r < k; ci++) {
        int c = colorder[ci], p = -1;
        for (int i = r; i < k; i++) if (bget(&R[i], c)) { p = i; break; }
        if (p < 0) continue;
        b72 t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < k; i++) if (i != r && bget(&R[i], c)) R[i] = bxor(R[i], R[r]);
        piv[r++] = c;
    }
    return r;
}
static long long cntw[73];
static void dfs(const b72 *g, int depth, int maxd, int start, b72 cur, const uint8_t *inI, int jside) {
    for (int t = start; t < 36; t++) {
        b72 nw = bxor(cur, g[t]);
        int keep = 1;
        if (jside) { int ni = 0; for (int i = 0; i < 72; i++) if (inI[i] && bget(&nw, i)) ni++; keep = ni > maxd; }
        if (keep) { int w = bwt(nw); if (w <= 12) cntw[w]++; }
        if (depth + 1 < maxd) dfs(g, depth + 1, maxd, t + 1, nw, inI, jside);
    }
}
static uint64_t rs;
static uint64_t rnd(void) { rs += 0x9e3779b97f4a7c15ULL; uint64_t z = rs; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
int main(int argc, char **argv) {
    golay_build();
    FILE *f = fopen(argv[1], "r"); long want = atol(argv[2]); rs = strtoull(argv[3], 0, 10) * 7777 + 1;
    static char line[16384]; long ln = -1; v24 E[12]; int got = 0;
    if (want < 0) { for (int t = 0; t < 12; t++) { E[t].a = GB[t]; E[t].b = 0; } got = 1; }   /* E = G24 (x) F4 */
    else while (fgets(line, sizeof line, f)) { if (++ln == want) { if (parse_rows_B(line, E, 12)) got = 1; break; } }
    if (!got) { fprintf(stderr, "no line\n"); return 1; }
    int pm[24]; for (int i = 0; i < 24; i++) pm[i] = i;
    if (strtoull(argv[3], 0, 10) != 0)
        for (int i = 23; i > 0; i--) { int j = (int)(rnd() % (uint64_t)(i + 1)); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
    uint32_t Gb[12]; for (int i = 0; i < 12; i++) Gb[i] = perm_apply(pm, GB[i]);
    uint32_t GWl[4096]; for (int m = 0; m < 4096; m++) { uint32_t w = 0; for (int i = 0; i < 12; i++) if ((m >> i) & 1) w ^= Gb[i]; GWl[m] = w; }
    /* generators of C */
    b72 R[36]; int k = 0;
    for (int i = 0; i < 12; i++) { b72 x = { 0, 0 }; for (int c = 0; c < 24; c++) if ((Gb[i] >> c) & 1) { bset(&x, 3 * c); bset(&x, 3 * c + 1); bset(&x, 3 * c + 2); } R[k++] = x; }
    for (int t = 0; t < 12; t++) { R[k++] = psiE(E[t]); R[k++] = psiE(vmulw(E[t])); }
    int so = 1, de = 1;
    for (int i = 0; i < 36; i++) { if (bwt(R[i]) % 4) de = 0; for (int j = i; j < 36; j++) if (bdot(R[i], R[j])) so = 0; }
    /* sigma-invariance: shift of each generator in C (check via rank) */
    b72 T[37]; int ord[72]; for (int i = 0; i < 72; i++) ord[i] = i; int piv[72];
    memcpy(T, R, sizeof(b72) * 36); int rk = rref72(T, 36, ord, piv);
    int inv = 1;
    for (int i = 0; i < 36; i++) { b72 S[37]; memcpy(S, T, sizeof(b72) * 36); S[36] = shift(R[i]); int pv2[72]; if (rref72(S, 37, ord, pv2) != rk) inv = 0; }
    /* psi(w x) == shift(psi(x)) */
    int lin = 1; for (int t = 0; t < 12; t++) { b72 a = psiE(vmulw(E[t])), b = shift(psiE(E[t])); if (a.lo != b.lo || a.hi != b.hi) lin = 0; }
    printf("rank=%d selforth=%d doublyeven_gens=%d sigma_invariant=%d psi(wx)=shift(psi x): %d\n", rk, so, de, inv, lin);
    /* direct count of weights <= 12: information set I = pivots of T, J = complement */
    uint8_t inI[72] = { 0 }; for (int i = 0; i < 36; i++) inI[piv[i]] = 1;
    int jo[72], nj = 0; for (int i = 0; i < 72; i++) if (!inI[i]) jo[nj++] = i;
    b72 U[36]; memcpy(U, T, sizeof(b72) * 36); int pj[72];
    int rJ = rref72(U, 36, jo, pj);
    memset(cntw, 0, sizeof cntw); b72 z = { 0, 0 };
    dfs(T, 0, 6, 0, z, inI, 0);
    dfs(U, 0, 6, 0, z, inI, 1);
    printf("J rank=%d direct counts: w4=%lld w8=%lld w12=%lld (w<4: %lld)\n", rJ, cntw[4], cntw[8], cntw[12], cntw[1] + cntw[2] + cntw[3]);
    /* formula count: all nonzero e of weight 8,10,12 (every scalar multiple) x all g */
    long long fc[73] = { 0 };
    long long v8a = 0, v8b = 0, v10 = 0, v12 = 0;
    /* enumerate all 4^12 words of E */
    for (long m = 1; m < (1L << 24); m++) {
        v24 x = { 0, 0 }; long mm = m;
        for (int t = 0; t < 12; t++) { int s = mm & 3; mm >>= 2; if (s) x = vadd(x, vscal(E[t], s)); }
        int w = vwt(x); if (w > 12) continue;
        uint32_t S = vsupp(x);
        for (int g = 0; g < 4096; g++) {
            int gw = __builtin_popcount(GWl[g]), t2 = __builtin_popcount(GWl[g] & S);
            int wt = 3 * gw + 2 * w - 4 * t2;
            if (wt <= 12) fc[wt]++;
        }
        /* projective violation counts (first nonzero coordinate value 1) */
        if (vget(x, __builtin_ctz(S)) != 1) continue;
        for (int o = 0; o < 759; o++) {
            uint32_t O = perm_apply(pm, OCT[o]); int t3 = __builtin_popcount(O & S);
            if (w == 8 && t3 == 8) v8a++;
            if (w == 8 && t3 == 7) v8b++;
            if (w == 10 && t3 == 8) v10++;
        }
        if (w == 12) for (int d = 0; d < 2576; d++) if (perm_apply(pm, DOD[d]) == S) v12++;
    }
    printf("formula counts: w4=%lld w8=%lld w12=%lld | violations: W8(=octad) %lld, W8(7) %lld, W10 %lld, W12 %lld -> 3x: w8=%lld w12=%lld\n",
           fc[4], fc[8], fc[12], v8a, v8b, v10, v12, 3 * v8a, 3 * (v8b + v10 + v12));
    int ok = (fc[4] == cntw[4] && fc[8] == cntw[8] && fc[12] == cntw[12] && cntw[4] == 0 && 3 * v8a == cntw[8] && 3 * (v8b + v10 + v12) == cntw[12] && rk == 36 && so && de && inv && lin);
    printf("RESULT %s\n", ok ? "OK" : "MISMATCH");
    return 0;
}
