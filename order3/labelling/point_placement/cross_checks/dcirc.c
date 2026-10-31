/* Hermitian self-dual double circulant [24,12] codes over F4: generator [I | A], A circulant with first row a,
   A conj(A)^T = I.  Writes those with minimum distance 8 (layout A).  Usage: dcirc OUT */
#include "../src/f4code.h"
int main(int argc, char **argv) {
    FILE *fo = fopen(argv[1], "w"); long npass = 0, nd8 = 0;
    vec *Aw = malloc(sizeof(vec) << 12), *Bw = malloc(sizeof(vec) << 12);
    for (u32 x = 0; x < (1u << 24); x++) {
        int a[12]; for (int i = 0; i < 12; i++) a[i] = (x >> (2 * i)) & 3;
        int ok = 1;
        for (int j = 0; j < 12 && ok; j++) { int s = 0; for (int i = 0; i < 12; i++) s ^= f4mul[a[i]][f4conj[a[(i + j) % 12]]]; if (s != (j == 0 ? 1 : 0)) ok = 0; }
        if (!ok) continue;
        npass++;
        vec g[12];
        for (int r = 0; r < 12; r++) { g[r].lo = g[r].hi = 0; vset(&g[r], r, 1); for (int i = 0; i < 12; i++) vset(&g[r], 12 + ((i + r) % 12), a[i]); }
        combos(g, 6, Aw); combos(g + 6, 6, Bw);
        int d = 99;
        for (long i = 0; i < 4096 && d >= 8; i++) for (long j = 0; j < 4096; j++) { if (!i && !j) continue; int w = __builtin_popcount((Aw[i].lo ^ Bw[j].lo) | (Aw[i].hi ^ Bw[j].hi)); if (w < d) { d = w; if (d < 8) break; } }
        if (d == 8) { nd8++; for (int r = 0; r < 12; r++) fprintf(fo, "%08x %08x ", g[r].lo, g[r].hi); fprintf(fo, "| double circulant a=%06x\n", x); }
    }
    fclose(fo); fprintf(stderr, "orthogonal first rows %ld, with d = 8: %ld\n", npass, nd8);
    return 0;
}
