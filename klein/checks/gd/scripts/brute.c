// Independent brute force for the instance format (NW <= 30): enumerate all assignments, check every word.
// Words are checked in order of increasing good-fraction (most restrictive first) for early exit.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
typedef struct { int d; u64 m[16]; int c[16]; unsigned char *good; double frac; } Word;
static int cmpw(const void *a, const void *b) { double x = ((Word*)a)->frac, y = ((Word*)b)->frac; return x < y ? -1 : x > y; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int NW, NWD; if (fscanf(f, "%d %d", &NW, &NWD) != 2) return 1;
    if (NW > 34) { fprintf(stderr, "NW too big\n"); return 1; }
    Word *W = calloc(NWD, sizeof(Word));
    for (int i = 0; i < NWD; i++) {
        int wt, d, ng; if (fscanf(f, "%d %d %d", &wt, &d, &ng) != 3) return 1;
        W[i].d = d; W[i].good = calloc(1 << d, 1);
        for (int t = 0; t < d; t++) { char hx[80]; if (fscanf(f, "%79s %d", hx, &W[i].c[t]) != 2) return 1; W[i].m[t] = strtoull(hx, NULL, 16); if (strlen(hx) > 16) { fprintf(stderr, "wide mask\n"); return 1; } }
        for (int k = 0; k < ng; k++) { int g; if (fscanf(f, "%d", &g) != 1) return 1; W[i].good[g] = 1; }
        W[i].frac = (double)ng / (double)(1 << d);
    }
    qsort(W, NWD, sizeof(Word), cmpw);
    long long nsol = 0;
    for (u64 x = 0; x < (1ULL << NW); x++) {
        int ok = 1;
        for (int i = 0; i < NWD && ok; i++) {
            int g = 0; for (int t = 0; t < W[i].d; t++) g |= ((__builtin_popcountll(W[i].m[t] & x) & 1) ^ W[i].c[t]) << t;
            if (!W[i].good[g]) ok = 0;
        }
        if (ok) { nsol++; printf("SOLUTION w=%016llx\n", x); }
    }
    printf("BRUTE nsol %lld\n", nsol);
    return 0;
}
