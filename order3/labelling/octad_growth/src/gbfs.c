/* Independent ground truth for the Golay-labelling tests: all labelled Golay codes containing the sextet
   {0-3},{4-7},...,{20-23}, by breadth-first orbit enumeration under S4 wr S6 (generators: (0 1), (0 1 2 3),
   the swap of the first two tetrads, the 6-cycle of tetrads), starting from a relabelled standard Golay code.
   Expected orbit size 4!^6 6! / |2^6:3.S6| = 995328.  Then, for forbidden tables dumped by gtest3 (files
   forb8.bin, forb12.bin of 2^21 bytes), counts the codes with all octads allowed and no forbidden dodecad and
   the sum of code_hash over them.  Usage: gbfs [forb8.bin forb12.bin] */
#include "gcore.h"

typedef struct { uint32_t r[12]; } code_t;
static void rref(uint32_t *R) {
    int r = 0;
    for (int c = 23; c >= 0 && r < 12; c--) {
        int p = -1; for (int i = r; i < 12; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint32_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 12; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
    if (r != 12) { fprintf(stderr, "rank %d\n", r); exit(1); }
}
#define HSZ (1u << 22)
static code_t *tab; static uint8_t *occ;
static uint64_t keyhash(const uint32_t *R) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < 12; i++) { h ^= R[i]; h *= 1099511628211ULL; } return h; }
static int insert(const uint32_t *R) {
    uint64_t h = keyhash(R) & (HSZ - 1);
    while (occ[h]) { if (!memcmp(tab[h].r, R, 48)) return 0; h = (h + 1) & (HSZ - 1); }
    occ[h] = 1; memcpy(tab[h].r, R, 48); return 1;
}
int main(int argc, char **argv) {
    gcore_init();
    tab = malloc(sizeof(code_t) * HSZ); occ = calloc(HSZ, 1);
    uint32_t W[4096]; golay_words(W);
    /* sextet of T = {0,1,2,3} in G0 */
    uint32_t T = 0xF, tet[6]; int nt = 0; tet[nt++] = T;
    for (int m = 0; m < 4096; m++) if (__builtin_popcount(W[m]) == 8 && (W[m] & T) == T) tet[nt++] = W[m] & ~T;
    if (nt != 6) { fprintf(stderr, "sextet size %d\n", nt); return 1; }
    int perm[24], k = 0;            /* point tet[i]'s j-th element -> 4i + j */
    for (int i = 0; i < 6; i++) { int j = 0; for (uint32_t t = tet[i]; t; t &= t - 1) perm[__builtin_ctz(t)] = 4 * i + j++; }
    (void)k;
    uint32_t gen[12]; golay_gen(gen);
    uint32_t B0[12]; for (int i = 0; i < 12; i++) B0[i] = applyperm(perm, gen[i]);
    rref(B0);
    int g[4][24];
    for (int i = 0; i < 24; i++) { g[0][i] = g[1][i] = g[2][i] = i; g[3][i] = (i + 4) % 24; }
    g[0][0] = 1; g[0][1] = 0;
    g[1][0] = 1; g[1][1] = 2; g[1][2] = 3; g[1][3] = 0;
    for (int i = 0; i < 4; i++) { g[2][i] = i + 4; g[2][i + 4] = i; }
    code_t *queue = malloc(sizeof(code_t) * 1100000); long qh = 0, qt = 0;
    insert(B0); memcpy(queue[qt++].r, B0, 48);
    while (qh < qt) {
        uint32_t *C = queue[qh++].r;
        for (int a = 0; a < 4; a++) {
            uint32_t R[12]; for (int i = 0; i < 12; i++) R[i] = applyperm(g[a], C[i]);
            rref(R);
            if (insert(R)) { if (qt >= 1100000) { fprintf(stderr, "queue overflow\n"); return 1; } memcpy(queue[qt++].r, R, 48); }
        }
    }
    printf("orbit size %ld (expected 995328)\n", qt);
    if (argc > 2) {
        FILE *f = fopen(argv[1], "rb"); if (fread(forb8, 1, F8BYTES, f) != F8BYTES) return 1; fclose(f);
        f = fopen(argv[2], "rb"); if (fread(forb12, 1, F12BYTES, f) != F12BYTES) return 1; fclose(f);
        long cnt = 0; uint64_t hs = 0;
        for (long q = 0; q < qt; q++) {
            uint32_t *C = queue[q].r; int ok = 1;
            for (int m = 1; m < 4096 && ok; m++) {
                uint32_t w = 0; for (int i = 0; i < 12; i++) if ((m >> i) & 1) w ^= C[i];
                int c = __builtin_popcount(w);
                if (c == 8 && F8(w)) ok = 0;
                if (c == 12 && F12(w)) ok = 0;
            }
            if (ok) { cnt++; hs += code_hash(C); }
        }
        printf("valid %ld hash %016llx\n", cnt, (unsigned long long)hs);
    }
    return 0;
}
