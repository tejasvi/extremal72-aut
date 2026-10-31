// All codewords of weight <= WMAX (default 14) of a binary [72,36] self-dual code given by 36 generator rows.
// Brouwer-Zimmermann with two complementary information sets I1, I2 (complement of an information set of a
// self-dual code is an information set; checked).  A word of weight <= 14 has <= 7 ones on I1 or on I2.
// Input (stdin): 36 lines "HI LO" (hex, bits 64..71 in HI, 0..63 in LO).  Output: "W HI LO weight" per word,
// deduplicated, then "COUNT n".
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int WMAX = 14, HALF = 7;
static inline int wt(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
static u128 *out; static long nout = 0, cap = 0;
static void emit(u128 c) { if (nout == cap) { cap = cap ? 2 * cap : 1024; out = realloc(out, cap * sizeof(u128)); } out[nout++] = c; }
static u128 R[36];
static void rec(int start, int depth, u128 cur) {
    for (int i = start; i < 36; i++) {
        u128 c = cur ^ R[i];
        if (wt(c) <= WMAX) emit(c);
        if (depth + 1 < HALF) rec(i + 1, depth + 1, c);
    }
}
// systematic form on the column set given by mask: returns 0 if columns in mask have rank < 36
static int systematic(const u128 *G, u128 mask, u128 *S) {
    u128 A[36]; memcpy(A, G, sizeof(A));
    int r = 0;
    for (int col = 0; col < 72 && r < 36; col++) {
        if (!((mask >> col) & 1)) continue;
        int p = -1; for (int i = r; i < 36; i++) if ((A[i] >> col) & 1) { p = i; break; }
        if (p < 0) continue;
        u128 t = A[p]; A[p] = A[r]; A[r] = t;
        for (int i = 0; i < 36; i++) if (i != r && ((A[i] >> col) & 1)) A[i] ^= A[r];
        r++;
    }
    if (r < 36) return 0;
    memcpy(S, A, sizeof(A));
    return 1;
}
static int cmp(const void *a, const void *b) { u128 x = *(const u128 *)a, y = *(const u128 *)b; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    if (argc > 1) { WMAX = atoi(argv[1]); HALF = WMAX / 2; }
    u128 G[36];
    for (int i = 0; i < 36; i++) {
        unsigned long long hi, lo; if (scanf("%llx %llx", &hi, &lo) != 2) { fprintf(stderr, "input\n"); return 1; }
        G[i] = ((u128)hi << 64) | lo;
    }
    u128 all = (((u128)1) << 72) - 1;
    // information set I1: greedy pivot columns over all 72
    u128 A[36]; memcpy(A, G, sizeof(A)); u128 I1 = 0; int r = 0;
    for (int col = 0; col < 72 && r < 36; col++) {
        int p = -1; for (int i = r; i < 36; i++) if ((A[i] >> col) & 1) { p = i; break; }
        if (p < 0) continue;
        u128 t = A[p]; A[p] = A[r]; A[r] = t;
        for (int i = 0; i < 36; i++) if (i != r && ((A[i] >> col) & 1)) A[i] ^= A[r];
        I1 |= ((u128)1) << col; r++;
    }
    if (r < 36) { printf("RANK %d\n", r); return 2; }
    u128 I2 = all & ~I1;
    u128 S1[36], S2[36];
    if (!systematic(G, I1, S1)) { printf("I1 not information set\n"); return 3; }
    if (!systematic(G, I2, S2)) { printf("I2 not information set\n"); return 3; }
    memcpy(R, S1, sizeof(R)); rec(0, 0, 0);
    memcpy(R, S2, sizeof(R)); rec(0, 0, 0);
    qsort(out, nout, sizeof(u128), cmp);
    long n = 0;
    for (long i = 0; i < nout; i++) {
        if (i && out[i] == out[i - 1]) continue;
        u128 c = out[i];
        printf("W %llx %llx %d\n", (unsigned long long)(c >> 64), (unsigned long long)c, wt(c)); n++;
    }
    printf("COUNT %ld\n", n);
    return 0;
}
