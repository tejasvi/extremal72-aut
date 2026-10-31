/* Exact level check for the E_B classification: for each class representative C (dim k) count the (k+1)-dim
   Hermitian self-orthogonal codes C' containing C with d(C') >= d:  ext(C) = #{nonzero cosets x + C in C^perp/C :
   <x,x> = 0, minwt(x + C) >= d} / 3.  Double counting pairs (C subset C') of labelled codes gives
     sum_{C' Mon-classes} ((4^{k+1}-1)/3) / |Aut(C')|  =  sum_{C Mon-classes} ext(C) / |Aut(C)|.
   Usage: ebext nb d classesfile [slice nslices]   prints "index ext aut" per class. */
#include "f4code.h"
int main(int argc, char **argv) {
    int nb = atoi(argv[1]), d = atoi(argv[2]);
    int slice = argc > 4 ? atoi(argv[4]) : 0, nsl = argc > 5 ? atoi(argv[5]) : 1;
    FILE *f = fopen(argv[3], "r"); char line[8192]; long idx = 0;
    while (fgets(line, sizeof line, f)) {
        long my = idx++;
        if (my % nsl != slice) continue;
        int k = atoi(line);
        char *p = strchr(line, ' ') + 1; p = strchr(p, ' ') + 1;
        char autstr[64]; sscanf(p, "%63s", autstr);
        p = strchr(p, ' ') + 1;
        f4v C[8];
        for (int r = 0; r < k; r++) { char t[9]; memcpy(t, p + 16 * r, 8); t[8] = 0; C[r].a = strtoul(t, 0, 16); memcpy(t, p + 16 * r + 8, 8); C[r].b = strtoul(t, 0, 16); }
        int pc[8]; f4rref(C, k, nb, pc, NULL);
        f4v D[32]; int dd = f4hermdual(C, k, nb, D);
        f4v R[32]; int nr = 0;
        for (int i = 0; i < dd; i++) { f4v x = D[i]; for (int j = 0; j < k; j++) { int e = f4get(x, pc[j]); if (e) x = f4add(x, f4smul(e, C[j])); } R[nr++] = x; }
        int pw[32]; int m = f4rref(R, nr, nb, pw, NULL);
        if (m != nb - 2 * k) { fprintf(stderr, "dim mismatch\n"); return 1; }
        int nwc = 1 << (2 * k); f4v cw[256];
        for (int t = 0; t < nwc; t++) { f4v x = { 0, 0 }; for (int j = 0; j < k; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, C[j])); cw[t] = x; }
        /* Gray-code walk over the 4^m cosets (F2 basis: R_j and w R_j) */
        f4v B[64]; int nbits = 0; for (int j = 0; j < m; j++) { B[nbits++] = R[j]; B[nbits++] = f4mw(R[j]); }
        long cnt = 0; f4v x = { 0, 0 };
        for (uint64_t g = 1; g < (1ULL << nbits); g++) {
            x = f4add(x, B[__builtin_ctzll(g)]);
            if (f4wt(x) & 1) continue;
            int ok = 1;
            for (int t = 0; t < nwc; t++) if (f4wt(f4add(x, cw[t])) < d) { ok = 0; break; }
            cnt += ok;
        }
        if (cnt % 3) { fprintf(stderr, "count %ld not divisible by 3\n", cnt); return 1; }
        printf("%ld %ld %s\n", my, cnt / 3, autstr); fflush(stdout);
    }
    return 0;
}
