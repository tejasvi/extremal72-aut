/* Positive control, part 2: for Hermitian self-dual [16,8,6] codes E over F4 count the labelled doubly-even
   self-dual binary [16,8,4] codes D on the same 16 coordinates with
     (V6) no weight-4 word of D inside a weight-6 support of E,
     (V8) no weight-8 word of D equal to a weight-8 support of E
   (length-48 analogue of W8/W10/W12: wt(tripled g + e) = 3|g| + 2wt(e) - 4|g & supp e| >= 12).
   All 9845550 labelled codes D are enumerated as the S16-orbits of e8+e8 (5791500) and d16+ (4054050) by BFS.
   For every passing pair the binary [48,24] code C = {(g,g,g)} + phi^{-1}(E) is built and its weight
   distribution computed.  Usage: lab16 codesfile   (lines: label and 8 rows %08x%08x; E on 16 coordinates) */
#include "../f4code.h"
typedef struct { uint16_t r[8]; } dcode;
static void rref16(uint16_t *R) {
    int r = 0;
    for (int c = 15; c >= 0 && r < 8; c--) {
        int p = -1; for (int i = r; i < 8; i++) if ((R[i] >> c) & 1) { p = i; break; }
        if (p < 0) continue;
        uint16_t t = R[p]; R[p] = R[r]; R[r] = t;
        for (int i = 0; i < 8; i++) if (i != r && ((R[i] >> c) & 1)) R[i] ^= R[r];
        r++;
    }
}
#define HS (1u << 25)
static dcode *tab; static uint8_t *occ;
static uint64_t hkey(const uint16_t *R) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < 8; i++) { h ^= R[i]; h *= 1099511628211ULL; } return h ^ (h >> 29); }
static int ins(const uint16_t *R) {
    uint64_t h = hkey(R) & (HS - 1);
    while (occ[h]) { if (!memcmp(tab[h].r, R, 16)) return 0; h = (h + 1) & (HS - 1); }
    occ[h] = 1; memcpy(tab[h].r, R, 16); return 1;
}
static uint16_t ap16(const int *p, uint16_t w) { uint16_t o = 0; for (int i = 0; i < 16; i++) if ((w >> i) & 1) o |= (uint16_t)(1u << p[i]); return o; }
static dcode *orbit(const uint16_t *start, long *size) {
    memset(occ, 0, HS);
    dcode *q = malloc(sizeof(dcode) * 6000000); long qh = 0, qt = 0;
    uint16_t R[8]; memcpy(R, start, 16); rref16(R); ins(R); memcpy(q[qt++].r, R, 16);
    int g[2][16]; for (int i = 0; i < 16; i++) { g[0][i] = i; g[1][i] = (i + 1) % 16; } g[0][0] = 1; g[0][1] = 0;
    while (qh < qt) {
        uint16_t *C = q[qh++].r;
        for (int a = 0; a < 2; a++) {
            uint16_t S[8]; for (int i = 0; i < 8; i++) S[i] = ap16(g[a], C[i]);
            rref16(S);
            if (ins(S)) memcpy(q[qt++].r, S, 16);
        }
    }
    *size = qt; return q;
}
int main(int argc, char **argv) {
    tab = malloc(sizeof(dcode) * HS); occ = malloc(HS);
    uint16_t e8e8[8] = { 0x000F, 0x0033, 0x0055, 0x00FF, 0x0F00, 0x3300, 0x5500, 0xFF00 };
    uint16_t d16p[8] = { 0x000F, 0x003C, 0x00F0, 0x03C0, 0x0F00, 0x3C00, 0xF000, 0x5555 };
    long n1, n2;
    dcode *O1 = orbit(e8e8, &n1); dcode *O2 = orbit(d16p, &n2);
    printf("orbit sizes: e8+e8 %ld (expected 5791500), d16+ %ld (expected 4054050)\n", n1, n2);
    FILE *f = fopen(argv[1], "r"); char line[4096];
    while (fgets(line, sizeof line, f)) {
        char label[256]; char hex[256];
        if (sscanf(line, "%255s %255s", label, hex) != 2) continue;
        f4v gen[8];
        for (int r = 0; r < 8; r++) { char t[9]; memcpy(t, hex + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, hex + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        /* all words of E */
        static uint8_t ft[65536], f8[65536]; memset(ft, 0, sizeof ft); memset(f8, 0, sizeof f8);
        int A[17] = { 0 };
        f4v B[16]; for (int i = 0; i < 8; i++) { B[2 * i] = gen[i]; B[2 * i + 1] = f4mw(gen[i]); }
        f4v cur = { 0, 0 };
        for (uint32_t gc = 1; gc < (1u << 16); gc++) {
            cur = f4add(cur, B[__builtin_ctz(gc)]);
            int w = f4wt(cur); A[w]++;
            uint16_t s = (uint16_t)f4supp(cur);
            if (w == 6) for (uint32_t m = 0; m < 65536; m = (m | ~s) + 1, m &= s) { if (__builtin_popcount(m) == 4) ft[m] = 1; if (m == s) break; }
            if (w == 8) f8[s] = 1;
        }
        int dmin = 0; for (int w = 1; w <= 16; w++) if (A[w]) { dmin = w; break; }
        long cnt[2] = { 0, 0 }; uint16_t ex[8]; int extype = -1;
        for (int t = 0; t < 2; t++) {
            dcode *O = t ? O2 : O1; long no = t ? n2 : n1;
            for (long q = 0; q < no; q++) {
                uint16_t *R = O[q].r; int ok = 1;
                for (uint32_t m = 1; m < 256 && ok; m++) {
                    uint16_t w = 0; for (int i = 0; i < 8; i++) if ((m >> i) & 1) w ^= R[i];
                    int c = __builtin_popcount(w);
                    if (c == 4 && ft[w]) ok = 0;
                    if (c == 8 && f8[w]) ok = 0;
                }
                if (ok) { cnt[t]++; if (extype < 0) { extype = t; memcpy(ex, R, 16); } }
            }
        }
        printf("%s: d(E)=%d A6=%d A8=%d  labelled D passing: e8+e8 %ld, d16+ %ld\n", label, dmin, A[6], A[8], cnt[0], cnt[1]);
        if (extype >= 0) {
            /* build C: coordinate 3i+j, cycle i; tripled D words and E words (F4 element -> cycle bits) */
            static const int bits3[4] = { 0, 5, 6, 3 };   /* element code -> b0 b1 b2 with (b0+b2)+(b1+b2)w = elt:
                                                            1 -> 011? check below */
            /* inverse of f4val(b0,b1,b2) = (b0^b2) | (b1^b2)<<1 over even-weight b */
            int tbl[4] = { -1, -1, -1, -1 };
            for (int b = 0; b < 8; b++) { int b0 = b & 1, b1 = (b >> 1) & 1, b2 = (b >> 2) & 1; if ((b0 + b1 + b2) % 2) continue; tbl[(b0 ^ b2) | ((b1 ^ b2) << 1)] = b; }
            (void)bits3;
            uint64_t G[24]; int ng = 0;
            for (int i = 0; i < 8; i++) { uint64_t w = 0; for (int c = 0; c < 16; c++) if ((ex[i] >> c) & 1) w |= 7ULL << (3 * c); G[ng++] = w; }
            for (int i = 0; i < 8; i++) for (int lam = 1; lam <= 2; lam++) {
                f4v x = lam == 1 ? gen[i] : f4mw(gen[i]); uint64_t w = 0;
                for (int c = 0; c < 16; c++) { int e = f4get(x, c); if (e) w |= (uint64_t)tbl[e] << (3 * c); }
                G[ng++] = w;
            }
            long WD[49] = { 0 }; uint64_t cw = 0;
            for (uint64_t gc = 1; gc < (1ULL << 24); gc++) { cw ^= G[__builtin_ctzll(gc)]; WD[__builtin_popcountll(cw)]++; }
            int so = 1; for (int i = 0; i < 24; i++) for (int j = 0; j < 24; j++) if (__builtin_popcountll(G[i] & G[j]) & 1) so = 0;
            printf("   example (%s): C = [48,24] self-orthogonal=%d, weight distribution:", extype ? "d16+" : "e8+e8", so);
            for (int w = 0; w <= 48; w++) if (WD[w] || w == 0) printf(" %d:%ld", w, w ? WD[w] : 1L);
            printf("\n");
        }
    }
    return 0;
}
