/* Independent verification of a csp5p solution: build the binary code C = F + E_bin of length 3m (m = 24 or 16)
   from a Hermitian self-dual F4 code E (m/2 generator rows) and a labelled binary code G' (m/2 basis words on
   E's coordinates; Golay code for m = 24), then compute dim, self-orthogonality, double evenness and the full
   weight distribution (hence the minimum weight) by enumerating all 2^dim codewords.
   Binary image of coordinate i: positions 3i,3i+1,3i+2; F4 value 1 -> 011, w -> 101, wbar -> 110 (F2-linear);
   G' word g -> 111 on every cycle i in g.
   Usage: verify_c M "E rows (layout A or B)" "g1,g2,...,gk (hex)" [PART NPARTS]   (PART/NPARTS split the work) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int hexv(int c) { return c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1; }
static int pc128(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }
int main(int argc, char **argv) {
    int m = atoi(argv[1]), k = m / 2; const char *es = argv[2], *gs = argv[3];
    int part = argc > 5 ? atoi(argv[4]) : 0, nparts = argc > 5 ? atoi(argv[5]) : 1;
    uint32_t lo[16], hi[16];
    /* parse E: layout B if first token has >= 16k hex digits, else layout A */
    const char *q = es; while (*q == ' ') q++;
    int tl = 0; while (q[tl] && q[tl] != ' ' && q[tl] != '|') tl++;
    if (tl >= 16 * k) { for (int r = 0; r < k; r++) { uint32_t a = 0, b = 0; for (int c = 0; c < 8; c++) a = a * 16 + hexv(q[16 * r + c]); for (int c = 0; c < 8; c++) b = b * 16 + hexv(q[16 * r + 8 + c]); lo[r] = a; hi[r] = b; } }
    else { char *e; const char *c = q; for (int r = 0; r < k; r++) { lo[r] = strtoul(c, &e, 16); c = e; hi[r] = strtoul(c, &e, 16); c = e; } }
    uint32_t g[16]; int ng = 0; { const char *c = gs; char *e; while (*c && ng < 16) { g[ng++] = strtoul(c, &e, 16); if (*e == ',') e++; c = e; if (e == c && !*e) break; } }
    if (ng != k) { fprintf(stderr, "need %d G' words, got %d\n", k, ng); return 1; }
    u128 gen[64]; int ngen = 0;
    for (int i = 0; i < k; i++) { u128 v = 0; for (int x = 0; x < m; x++) if ((g[i] >> x) & 1) v |= (u128)7 << (3 * x); gen[ngen++] = v; }
    static const int pat[4] = { 0, 6 /*011: bits1,2*/, 5 /*101: bits0,2*/, 3 /*110: bits0,1*/ };
    /* bit order within a cycle: position 3x+j <-> bit j of the 3-bit pattern (u0 at j=0) : 011 = u0=0,u1=1,u2=1 -> bits 1,2 */
    for (int r = 0; r < k; r++) for (int lam = 1; lam <= 2; lam++) {
        u128 v = 0;
        for (int x = 0; x < m; x++) {
            int c = ((lo[r] >> x) & 1) | (((hi[r] >> x) & 1) << 1);
            if (lam == 2) { static const int mw[4] = {0, 2, 3, 1}; c = mw[c]; }   /* times w */
            v |= (u128)pat[c] << (3 * x);
        }
        gen[ngen++] = v;
    }
    /* rank (Gaussian elimination) */
    u128 bas[64]; int nb = 0;
    for (int i = 0; i < ngen; i++) { u128 v = gen[i]; for (int j = 0; j < nb; j++) { int hb = 127; while (!((bas[j] >> hb) & 1)) hb--; if ((v >> hb) & 1) v ^= bas[j]; }
        if (v) { bas[nb++] = v; for (int a = nb - 1; a > 0; a--) { int h1 = 127, h0 = 127; while (!((bas[a] >> h1) & 1)) h1--; while (!((bas[a - 1] >> h0) & 1)) h0--; if (h1 > h0) { u128 t = bas[a]; bas[a] = bas[a - 1]; bas[a - 1] = t; } else break; } } }
    int so = 1, de = 1; for (int i = 0; i < ngen; i++) { if (pc128(gen[i]) % 4) de = 0; for (int j = 0; j < ngen; j++) if (pc128(gen[i] & gen[j]) & 1) so = 0; }
    printf("length %d generators %d rank %d self_orthogonal %d generators_doubly_even %d\n", 3 * m, ngen, nb, so, de);
    if (nb != m * 3 / 2) { printf("NOT SELF-DUAL DIMENSION\n"); }
    /* enumerate: inner = first min(20, nb) basis vectors, outer = rest */
    int ni = nb < 20 ? nb : 20, no = nb - ni;
    u128 *tab = malloc(sizeof(u128) << ni); tab[0] = 0;
    for (int i = 0; i < ni; i++) for (long j = 0; j < (1L << i); j++) tab[(1L << i) + j] = tab[j] ^ bas[i];
    long hist[129] = {0};
    long nout = 1L << no, per = (nout + nparts - 1) / nparts, o0 = part * per, o1 = o0 + per < nout ? o0 + per : nout;
    for (long o = o0; o < o1; o++) {
        u128 base = 0; for (int j = 0; j < no; j++) if ((o >> j) & 1) base ^= bas[ni + j];
        for (long i = 0; i < (1L << ni); i++) hist[pc128(base ^ tab[i])]++;
    }
    int dmin = 999; for (int w = 1; w <= 3 * m; w++) if (hist[w]) { dmin = w; break; }
    if (part == 0 && nparts == 1) hist[0] -= 0;
    printf("part %d/%d outer %ld..%ld  minimum nonzero weight %d  weights:", part, nparts, o0, o1, dmin);
    for (int w = 0; w <= 3 * m; w++) if (hist[w]) printf(" %d:%ld", w, hist[w]);
    printf("\n");
    return 0;
}
