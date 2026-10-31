/* c3class key (cform canon_class via ckey.c) for each E_B line of an ebcls2 file: prints "cfkey cfaut cfsc".
   usage: ebkey NB KB D FILE */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int c3c_class_key(const unsigned *lo, const unsigned *hi, int k, int n, int d, unsigned *klo, unsigned *khi,
                  double *aut, int *sc);
int main(int argc, char **argv) {
    int NB = atoi(argv[1]), KB = atoi(argv[2]), D = atoi(argv[3]);
    FILE *f = fopen(argv[4], "r"); char line[4096];
    while (fgets(line, sizeof line, f)) {
        unsigned lo[16], hi[16], klo[16], khi[16]; char *q = line;
        for (int r = 0; r < KB; r++) { char h1[9], h2[9]; memcpy(h1, q, 8); h1[8] = 0; memcpy(h2, q + 8, 8); h2[8] = 0; q += 16; lo[r] = strtoul(h1, NULL, 16); hi[r] = strtoul(h2, NULL, 16); }
        double aut; int sc;
        if (c3c_class_key(lo, hi, KB, NB, D, klo, khi, &aut, &sc)) { fprintf(stderr, "cform failed\n"); return 1; }
        for (int r = 0; r < KB; r++) printf("%08x%08x", klo[r], khi[r]);
        printf(" %.0f %d\n", aut, sc);
    }
    return 0;
}
