/* sample random t.i. [nb,k,>=d] codes, report class keys not in a classes file */
#include "cform.h"
int main(int argc, char **argv) {
    int nb = atoi(argv[1]), k = atoi(argv[2]), dmin = atoi(argv[3]); long ns = atol(argv[4]);
    FILE *f = fopen(argv[5], "r"); char line[8192];
    f4v keys[100000][6]; int nk = 0;
    while (fgets(line, sizeof line, f)) { char *p = strchr(line, ' ') + 1; for (int r = 0; r < k; r++) { char t[9]; memcpy(t, p + 16 * r, 8); t[8] = 0; keys[nk][r].a = strtoul(t, 0, 16); memcpy(t, p + 16 * r + 8, 8); keys[nk][r].b = strtoul(t, 0, 16); } nk++; }
    rng_t R; rng_seed(&R, 7);
    long tested = 0, miss = 0;
    for (long s = 0; s < ns; s++) {
        f4v gen[8]; int kk = 0;
        while (kk < k) {
            f4v W[32]; int dw = f4hermdual(gen, kk, nb, W);
            for (;;) { f4v v = { 0, 0 }; for (int i = 0; i < dw; i++) v = f4add(v, f4smul((int)(rng_next(&R) & 3), W[i]));
                if (f4iszero(v) || (f4wt(v) & 1)) continue; gen[kk] = v; if (f4rank(gen, kk + 1, nb) == kk + 1) break; }
            kk++;
        }
        int ok = 1;
        for (uint64_t t = 1; t < (1ULL << (2 * k)) && ok; t++) { f4v x = { 0, 0 }; for (int j = 0; j < k; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, gen[j])); if (f4wt(x) < dmin) ok = 0; }
        if (!ok) continue;
        tested++;
        f4v key[8]; double a; int sc;
        canon_class(gen, k, nb, 1, key, &a, &sc);
        int found = 0; for (int j = 0; j < nk; j++) if (!mat_cmp(keys[j], key, k)) { found = 1; break; }
        if (!found) {
            miss++;
            if (miss <= 5) {
                printf("missing: aut=%.0f gen:", a);
                for (int r = 0; r < k; r++) { printf(" "); f4print(stdout, gen[r], nb); }
                /* weight distribution */
                int A[33] = { 0 };
                for (uint64_t t = 1; t < (1ULL << (2 * k)); t++) { f4v x = { 0, 0 }; for (int j = 0; j < k; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, gen[j])); A[f4wt(x)]++; }
                printf("  wd:"); for (int w = 0; w <= nb; w++) if (A[w]) printf(" %d:%d", w, A[w]);
                int zc = 0; uint32_t sup = 0; for (int r = 0; r < k; r++) sup |= f4supp(gen[r]); zc = nb - __builtin_popcount(sup);
                printf("  zerocols=%d\n", zc);
            }
        }
    }
    printf("tested %ld missing %ld (%.4f)\n", tested, miss, (double)miss / tested);
    return 0;
}
