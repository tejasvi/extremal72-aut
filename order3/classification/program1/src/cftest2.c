/* canonical form sanity: random t.i. [nb,k,>=d] codes; key(C) == key(mu C) for random monomial mu and conj */
#include "cform.h"
int main(int argc, char **argv) {
    int nb = atoi(argv[1]), k = atoi(argv[2]), dmin = atoi(argv[3]); long ns = atol(argv[4]);
    rng_t R; rng_seed(&R, 99);
    long bad = 0, tested = 0;
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
        f4v key1[8], key2[8]; double a1, a2; int s1, s2;
        canon_class(gen, k, nb, 1, key1, &a1, &s1);
        /* random monomial map + random basis change + maybe conj */
        int perm[32]; for (int i = 0; i < nb; i++) perm[i] = i;
        for (int i = nb - 1; i > 0; i--) { int j = rng_next(&R) % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        int sc[32]; for (int i = 0; i < nb; i++) sc[i] = 1 + rng_next(&R) % 3;
        int cj = rng_next(&R) & 1;
        f4v g2[8];
        for (int r = 0; r < k; r++) {
            f4v x = { 0, 0 };
            for (int i = 0; i < nb; i++) { int e = f4get(gen[r], i); if (e) { if (cj) e = F4CONJ[e]; f4set(&x, perm[i], F4MUL[e][sc[i]]); } }
            g2[r] = x;
        }
        /* basis change */
        for (int r = 0; r < k; r++) for (int r2 = 0; r2 < k; r2++) if (r != r2 && (rng_next(&R) & 1)) g2[r] = f4add(g2[r], f4smul(1 + rng_next(&R) % 3, g2[r2]));
        canon_class(g2, k, nb, 1, key2, &a2, &s2);
        if (mat_cmp(key1, key2, k) || a1 != a2) bad++;
    }
    printf("nb=%d k=%d d>=%d: tested %ld, mismatches %ld\n", nb, k, dmin, tested, bad);
    return 0;
}
