/* Brute-force weight distribution of a binary linear code of length N <= 128 and dimension K <= 40.
 * Input file: first line "N K", then K lines each with two hex numbers "hi lo" (bit i of the 128-bit value =
 * coordinate i). Enumerates all 2^K codewords in Gray-code order. Prints the weight distribution and the rank
 * check (all codewords distinct is implied by rank K, verified by Gaussian elimination first).
 * usage: mincheck FILE
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
    if (argc < 2) return 1;
    FILE *f = fopen(argv[1], "r");
    int N, K, ncode = 0;
    if (!f) return 1;
    while (fscanf(f, "%d %d", &N, &K) == 2) {
    if (N > 128 || K > 40) { fprintf(stderr, "bad input\n"); return 1; }
    ncode++;
    uint64_t hi[40], lo[40];
    for (int i = 0; i < K; i++) {
        unsigned long long a, b;
        if (fscanf(f, "%llx %llx", &a, &b) != 2) { fprintf(stderr, "bad row\n"); return 1; }
        hi[i] = a; lo[i] = b;
    }
    /* rank check */
    uint64_t h2[40], l2[40];
    for (int i = 0; i < K; i++) { h2[i] = hi[i]; l2[i] = lo[i]; }
    int rk = 0;
    for (int bit = 0; bit < 128 && rk < K; bit++) {
        int piv = -1;
        for (int i = rk; i < K; i++) {
            int b = bit < 64 ? (int)((l2[i] >> bit) & 1) : (int)((h2[i] >> (bit - 64)) & 1);
            if (b) { piv = i; break; }
        }
        if (piv < 0) continue;
        uint64_t th = h2[piv], tl = l2[piv]; h2[piv] = h2[rk]; l2[piv] = l2[rk]; h2[rk] = th; l2[rk] = tl;
        for (int i = 0; i < K; i++) if (i != rk) {
            int b = bit < 64 ? (int)((l2[i] >> bit) & 1) : (int)((h2[i] >> (bit - 64)) & 1);
            if (b) { h2[i] ^= h2[rk]; l2[i] ^= l2[rk]; }
        }
        rk++;
    }
    printf("N %d K %d rank %d\n", N, K, rk);
    if (rk != K) { printf("RANK_DEFICIENT\n"); continue; }
    unsigned long long wd[129] = {0};
    uint64_t ch = 0, cl = 0;
    wd[0] = 1;
    unsigned long long total = 1ULL << K;
    for (unsigned long long i = 1; i < total; i++) {
        int j = __builtin_ctzll(i);
        ch ^= hi[j]; cl ^= lo[j];
        wd[__builtin_popcountll(ch) + __builtin_popcountll(cl)]++;
    }
    int dmin = -1;
    for (int w = 1; w <= N; w++) if (wd[w]) { dmin = w; break; }
    printf("MINWEIGHT %d\n", dmin);
    printf("WD");
    for (int w = 0; w <= N; w++) if (wd[w]) printf(" %d:%llu", w, wd[w]);
    printf("\n");
    }
    fclose(f);
    printf("CODES %d\n", ncode);
    return 0;
}
