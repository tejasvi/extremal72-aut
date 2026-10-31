/* Monte Carlo check of a classification of Hermitian self-orthogonal [nb,k,>=d] codes: sample uniform totally
   isotropic k-subspaces (successive uniform isotropic vectors in the dual), estimate P(d >= dmin), and compare
   N_ti(nb,k) * P with sum over classes of |Mon|/|Aut| (classes file: lines "k key aut gen").
   Usage: tisample nb k dmin nsamples seed classesfile */
#include "f4code.h"
#include <math.h>
int main(int argc, char **argv) {
    int nb = atoi(argv[1]), k = atoi(argv[2]), dmin = atoi(argv[3]); long ns = atol(argv[4]); uint64_t seed = strtoull(argv[5], 0, 10);
    rng_t R; rng_seed(&R, seed);
    long good = 0;
    for (long s = 0; s < ns; s++) {
        f4v gen[16]; int kk = 0;
        while (kk < k) {
            f4v W[32]; int dw = f4hermdual(gen, kk, nb, W);
            for (;;) {
                f4v v = { 0, 0 };
                for (int i = 0; i < dw; i++) v = f4add(v, f4smul((int)(rng_next(&R) & 3), W[i]));
                if (f4iszero(v) || (f4wt(v) & 1)) continue;
                gen[kk] = v;
                if (f4rank(gen, kk + 1, nb) == kk + 1) break;
            }
            kk++;
        }
        int ok = 1;
        for (uint64_t t = 1; t < (1ULL << (2 * k)) && ok; t++) {
            f4v x = { 0, 0 }; for (int j = 0; j < k; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, gen[j]));
            if (f4wt(x) < dmin) ok = 0;
        }
        good += ok;
    }
    /* number of t.i. k-subspaces */
    long double ordered = 1;
    for (int i = 0; i < k; i++) { int m = nb - 2 * i; long double I = (powl(2, m) - (m % 2 ? -1 : 1)) * (powl(2, m - 1) + (m % 2 ? -1 : 1)); ordered *= I * powl(4, i); }
    long double gl = 1; for (int i = 0; i < k; i++) gl *= powl(4, k) - powl(4, i);
    long double Nti = ordered / gl;
    long double mon = powl(3, nb); for (int i = 2; i <= nb; i++) mon *= i;
    long double p = (long double)good / ns, sd = sqrtl(p * (1 - p) / ns);
    long double sum = 0; long nc = 0;
    FILE *f = fopen(argv[6], "r"); char line[8192];
    while (fgets(line, sizeof line, f)) { char *q = strchr(line, ' ') + 1; q = strchr(q, ' ') + 1; double a = atof(q); char *e = q; while (*e >= '0' && *e <= '9') e++; int two = (e[0] == 'x' && e[1] == '2'); sum += (two ? 2 : 1) * mon / a; nc++; }
    printf("nb=%d k=%d d>=%d: N_ti=%.6Le P(d)=%.5Lf+-%.5Lf => expected %.5Le +- %.2Le; classes %ld give %.5Le (ratio %.4Lf)\n", nb, k, dmin, Nti, p, sd, Nti * p, Nti * sd, nc, sum, sum / (Nti * p));
    return 0;
}
