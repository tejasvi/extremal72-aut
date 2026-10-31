/* stabcount ACT REPS MIN: for every rep "0 x" of REPS print "x st" when st = #{g : A_g x + c_g = x} >= MIN.
 * ACT: int32 ng, int32 nx, then ng blocks of nx row masks (uint64) + constant (uint64). Byte tables per g. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "stabcount ACT REPS MIN\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int ng, nx;
    if (!f || fread(&ng, 4, 1, f) != 1 || fread(&nx, 4, 1, f) != 1 || nx > 40) { fprintf(stderr, "act\n"); return 1; }
    uint64_t *rows = malloc(8 * (size_t)ng * nx), *cst = malloc(8 * (size_t)ng);
    for (int g = 0; g < ng; g++)
        if ((int)fread(rows + (size_t)g * nx, 8, nx, f) != nx || fread(cst + g, 8, 1, f) != 1) { fprintf(stderr, "act\n"); return 1; }
    fclose(f);
    int NB = (nx + 7) / 8, mn = atoi(argv[3]);
    uint64_t *tab = malloc(8 * (size_t)ng * NB * 256);
    for (int g = 0; g < ng; g++) {
        uint64_t col[64];
        for (int j = 0; j < nx; j++) { uint64_t c = 0; for (int i = 0; i < nx; i++) if ((rows[(size_t)g * nx + i] >> j) & 1) c |= 1ULL << i; col[j] = c; }
        for (int b = 0; b < NB; b++) for (int v = 0; v < 256; v++) {
            uint64_t y = b == 0 ? cst[g] : 0;
            for (int q = 0; q < 8; q++) if (((v >> q) & 1) && 8 * b + q < nx) y ^= col[8 * b + q];
            tab[((size_t)g * NB + b) * 256 + v] = y;
        }
    }
    FILE *rf = fopen(argv[2], "r"); unsigned long long hi, x; long long n = 0, hist[4096] = {0};
    while (fscanf(rf, "%llx %llx", &hi, &x) == 2) {
        int st = 0;
        for (int g = 0; g < ng; g++) {
            const uint64_t *t = tab + (size_t)g * NB * 256; uint64_t y = 0;
            for (int b = 0; b < NB; b++) y ^= t[b * 256 + ((x >> (8 * b)) & 255)];
            if (y == x) st++;
        }
        n++; if (st < 4096) hist[st]++;
        if (st >= mn) printf("%llx %d\n", x, st);
    }
    fprintf(stderr, "reps %lld; stabilizer histogram:", n);
    for (int i = 1; i < 4096; i++) if (hist[i]) fprintf(stderr, " %d:%lld", i, hist[i]);
    fprintf(stderr, "\n");
    return 0;
}
