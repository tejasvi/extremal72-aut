/* Auditor test (rev_reclass): invariance of the E_B class key (mycanon.h mc_class) under random monomial maps,
   conjugation and basis changes; also compares |Aut| and selfconj with the stored values.
   usage: ebinv FILE K NB NTRANS STEP SEED   (tests every STEP-th line) */
#include "mycanon.h"
static u64 st = 88172645463325252ULL;
static u64 rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int K = atoi(argv[2]), NB = atoi(argv[3]), ntr = atoi(argv[4]), step = atoi(argv[5]);
    st ^= (u64)atol(argv[6]) * 0x9E3779B97F4A7C15ULL;
    char line[8192]; long li = -1, nt = 0, bad = 0;
    while (fgets(line, sizeof line, f)) {
        li++; if (li % step) continue;
        vec g[16]; char *q = line;
        for (int r = 0; r < K; r++) { char h[9]; memcpy(h, q, 8); h[8] = 0; g[r].lo = strtoul(h, 0, 16); memcpy(h, q + 8, 8); h[8] = 0; g[r].hi = strtoul(h, 0, 16); q += 16; }
        double aut; int sc; sscanf(q, "%lf %d", &aut, &sc);
        for (int t = 0; t < ntr; t++) {
            int perm[32]; for (int i = 0; i < NB; i++) perm[i] = i; for (int i = NB - 1; i > 0; i--) { int j = rnd() % (i + 1); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
            int mu[32]; for (int i = 0; i < NB; i++) mu[i] = 1 + rnd() % 3; int cj = rnd() & 1;
            vec h[16]; for (int r = 0; r < K; r++) { vec y = {0, 0}; for (int i = 0; i < NB; i++) { int c = vget(g[r], i); if (c) vset(&y, perm[i], f4mul[c][mu[i]]); } if (cj) { y.lo ^= y.hi; } h[r] = y; }
            for (int r = 0; r < K; r++) for (int s = 0; s < K; s++) if (r != s && (rnd() & 3) == 0) h[r] = vadd(h[r], vscal(1 + rnd() % 3, h[s]));
            vec key[16]; double a2; int s2; mc_class(h, K, NB, key, &a2, &s2); nt++;
            int eq = 1; for (int r = 0; r < K; r++) if (key[r].lo != g[r].lo || key[r].hi != g[r].hi) eq = 0;
            if (!eq || a2 != aut || s2 != sc) { bad++; fprintf(stderr, "FAIL line %ld trans %d eq %d aut %.0f/%.0f sc %d/%d\n", li, t, eq, a2, aut, s2, sc); }
        }
    }
    printf("tests %ld failures %ld\n", nt, bad);
    return 0;
}
