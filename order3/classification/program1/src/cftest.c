/* classify random Hermitian self-dual codes of length n with d >= dmin by canonical class keys */
#include "cform.h"
typedef struct { int n; uint64_t A[33]; } cnt_t;
static void count_cb(f4v w, int nrows, void *c) { ((cnt_t *)c)->A[f4wt(w)]++; }
int main(int argc, char **argv) {
    int n = atoi(argv[1]), dmin = atoi(argv[2]); long ns = atol(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
    rng_t R; rng_seed(&R, seed);
    int k = n / 2;
    f4v keys[1000][16]; double auts[1000]; long cnts[1000]; int nkeys = 0; long found = 0;
    double massum = 0;
    for (long s = 0; s < ns; s++) {
        f4v gen[16]; random_sd(&R, n, gen);
        cnt_t C; memset(&C, 0, sizeof C);
        sd_lowwords(gen, n, dmin - 1, count_cb, &C);
        int bad = 0; for (int w = 1; w < dmin; w++) if (C.A[w]) bad = 1;
        if (bad) continue;
        found++;
        f4v key[16]; double az; int sc;
        if (canon_class(gen, k, n, dmin, key, &az, &sc)) { printf("canon failed\n"); return 1; }
        int j; for (j = 0; j < nkeys; j++) if (!mat_cmp(keys[j], key, k)) break;
        if (j == nkeys) { memcpy(keys[nkeys], key, sizeof(f4v) * k); auts[nkeys] = az; cnts[nkeys] = 0; nkeys++; }
        cnts[j]++;
    }
    printf("n=%d d>=%d: %ld codes from %ld samples, %d classes (Mon x conj)\n", n, dmin, found, ns, nkeys);
    for (int j = 0; j < nkeys; j++) printf("  class %d: |Aut_Mon|=%.0f count=%ld hash=%016llx\n", j, auts[j], cnts[j], (unsigned long long)mat_hash(keys[j], k));
    return 0;
}
