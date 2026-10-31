/* Sample uniformly random Hermitian self-dual codes of length n over F4; histogram of minimum distance and (for
   d = dmax) of A_dmax; optionally save the codes with d >= dsave.  Self-test: low-weight counts vs full weight
   distribution on the first few codes.
   Usage: rsd n nsamples seed [dsave savefile] */
#include "f4code.h"
typedef struct { int n; uint64_t A[33]; } cnt_t;
static void count_cb(f4v w, int nrows, void *c) { ((cnt_t *)c)->A[f4wt(w)]++; }
int main(int argc, char **argv) {
    int n = atoi(argv[1]); long ns = atol(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
    int dsave = argc > 4 ? atoi(argv[4]) : 99; FILE *fs = argc > 5 ? fopen(argv[5], "w") : NULL;
    rng_t R; rng_seed(&R, seed);
    long dh[33] = { 0 }; static long ah[33][4000];
    int W = 2 * (n / 6) + 2; if (W > n) W = n;   /* extremal bound; enumerate words of weight <= W */
    for (long s = 0; s < ns; s++) {
        f4v gen[16];
        random_sd(&R, n, gen);
        cnt_t C; memset(&C, 0, sizeof C);
        sd_lowwords(gen, n, W, count_cb, &C);
        if (s < 3 && n <= 24) {
            uint64_t A[33]; full_wd(gen, n / 2, n, A);
            for (int w = 0; w <= W; w++) if (w > 0 && A[w] != C.A[w]) { fprintf(stderr, "MISMATCH w=%d %lu %lu\n", w, A[w], C.A[w]); return 1; }
            fprintf(stderr, "selftest ok:"); for (int w = 0; w <= n; w++) if (A[w]) fprintf(stderr, " A%d=%lu", w, A[w]); fprintf(stderr, "\n");
        }
        int d = 0;
        for (int w = 1; w <= W; w++) if (C.A[w]) { d = w; break; }
        if (!d) d = W + 1;
        dh[d]++;
        if (d <= W && C.A[d] < 4000) ah[d][C.A[d]]++;
        if (fs && d >= dsave) {
            for (int i = 0; i < n / 2; i++) fprintf(fs, "%08x%08x", gen[i].a, gen[i].b);
            fprintf(fs, " %d %lu\n", d, C.A[d]);
        }
    }
    printf("n=%d samples=%ld seed=%lu W=%d\n", n, ns, seed, W);
    for (int d = 0; d <= 32; d++) if (dh[d]) printf("d=%d%s: %ld\n", d, d == W + 1 ? "+" : "", dh[d]);
    for (int d = 0; d <= W; d++) if (dh[d]) {
        printf("A_d histogram for d=%d:", d);
        for (int a = 0; a < 4000; a++) if (ah[d][a]) printf(" %d:%ld", a, ah[d][a]);
        printf("\n");
    }
    if (fs) fclose(fs);
    return 0;
}
