/* Convert a raw 2^24-bit subset bitmap (bit m = mask m) into the compact rank-indexed layout of c3class gcore.h
   (bit r = colex rank among s-subsets, ceil(C(24,s)/8) bytes).  Usage: raw2compact S IN OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint32_t binom[33][33];
static uint32_t rankset(uint32_t m) { uint32_t r = 0; int i = 1; while (m) { int p = __builtin_ctz(m); m &= m - 1; r += binom[p][i++]; } return r; }
int main(int argc, char **argv) {
    for (int a = 0; a <= 32; a++) { binom[a][0] = 1; for (int b = 1; b <= 32; b++) binom[a][b] = a ? binom[a - 1][b - 1] + binom[a - 1][b] : 0; }
    int s = atoi(argv[1]); unsigned char *raw = malloc(1 << 21);
    FILE *f = fopen(argv[2], "rb"); if (fread(raw, 1, 1 << 21, f) != (1 << 21)) return 1; fclose(f);
    long nb = ((long)binom[24][s] + 7) / 8; unsigned char *c = calloc(nb, 1); long cnt = 0, bad = 0;
    for (uint32_t m = 0; m < (1u << 24); m++) if ((raw[m >> 3] >> (m & 7)) & 1) { if (__builtin_popcount(m) != s) { bad++; continue; } uint32_t r = rankset(m); c[r >> 3] |= 1 << (r & 7); cnt++; }
    f = fopen(argv[3], "wb"); fwrite(c, 1, nb, f); fclose(f);
    fprintf(stderr, "%s: %ld sets of size %d (ignored %ld of other sizes) -> %ld bytes\n", argv[2], cnt, s, bad, nb);
    return 0;
}
