/* verify.c -- brute-force verification of matrices printed as "SOL K0=k r0 r1 ... r6" (rows in position order):
 * unitarity and M(a) + M(aU) >= THR for every nonzero a in GF(16)^7 (no symmetry reduction).
 * usage: verify THR < file */
#include "common.h"
#include <omp.h>
static int all_ok(const uint32_t *U) {
    uint32_t mult[7][16];
    for (int j = 0; j < 7; j++) for (int c = 0; c < 16; c++) mult[j][c] = smul(c, U[j]);
    int bad = 0;
    #pragma omp parallel for reduction(|:bad) schedule(static)
    for (uint32_t hi = 0; hi < (1u << 12); hi++) {          /* a = (hi << 16) | lo, all 2^28 - 1 nonzero a */
        if (bad) continue;
        uint32_t vh = 0;
        for (int j = 4; j < 7; j++) vh ^= mult[j][(hi >> (4 * (j - 4))) & 15];
        for (uint32_t lo = 0; lo < (1u << 16); lo++) {
            uint32_t a = (hi << 16) | lo; if (!a) continue;
            uint32_t v = vh ^ mult[0][lo & 15] ^ mult[1][(lo >> 4) & 15] ^ mult[2][(lo >> 8) & 15] ^ mult[3][(lo >> 12) & 15];
            if (Mvec(a) + Mvec(v) < THR) { bad = 1; break; }
        }
    }
    return !bad;
}
int main(int argc, char **argv) {
    common_init(atoi(argv[1]));
    char line[512]; long n = 0, good = 0;
    while (fgets(line, sizeof line, stdin)) {
        if (strncmp(line, "SOL", 3)) continue;
        uint32_t U[7]; char *p = strchr(line, ' '); p = strchr(p + 1, ' ');
        for (int i = 0; i < 7; i++) U[i] = strtoul(p, &p, 16);
        int unit = 1;
        for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) if (herm(U[i], U[j]) != (i == j)) unit = 0;
        int ok = unit && all_ok(U);
        n++; good += ok;
        if (!ok) { printf("INVALID: %s", line); fflush(stdout); }
    }
    printf("verified %ld matrices: %ld valid (unitary and (*) with THR=%d for all a != 0), %ld invalid\n", n, good, THR, n - good);
    return 0;
}
