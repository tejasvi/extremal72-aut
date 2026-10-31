#include "../cform.h"
int main(void) {
    FILE *f = fopen("codes16.txt", "r"); char line[4096];
    while (fgets(line, sizeof line, f)) {
        char label[256], hex[256]; sscanf(line, "%255s %255s", label, hex);
        f4v g[8]; for (int r = 0; r < 8; r++) { char t[9]; memcpy(t, hex + 16 * r, 8); t[8] = 0; g[r].a = strtoul(t, 0, 16); memcpy(t, hex + 16 * r + 8, 8); g[r].b = strtoul(t, 0, 16); }
        f4v key[8]; double a; int sc; canon_class(g, 8, 16, 6, key, &a, &sc);
        printf("%-14s aut=%.0f selfconj=%d key hash %016llx\n", label, a, sc, (unsigned long long)mat_hash(key, 8));
    }
    /* D of QR48: weight-4 words and their union structure */
    uint16_t D[8] = { 0xffff, 0x004b, 0x0194, 0x022a, 0x0429, 0x1890, 0x2814, 0x4884 };
    int n4 = 0; uint16_t w4[64];
    for (int m = 1; m < 256; m++) { uint16_t w = 0; for (int i = 0; i < 8; i++) if ((m >> i) & 1) w ^= D[i]; if (__builtin_popcount(w) == 4) w4[n4++] = w; }
    /* connected components of the "overlap" graph on weight-4 words */
    uint16_t comp[64]; int nc = 0;
    for (int i = 0; i < n4; i++) { int j; for (j = 0; j < nc; j++) if (comp[j] & w4[i]) break; if (j == nc) comp[nc++] = w4[i]; else comp[j] |= w4[i]; }
    /* merge components */
    for (int it = 0; it < 5; it++) for (int i = 0; i < nc; i++) for (int j = i + 1; j < nc; j++) if (comp[i] & comp[j]) { comp[i] |= comp[j]; comp[j] = comp[--nc]; j = i; }
    printf("D (QR48): %d weight-4 words, supports of components:", n4); for (int i = 0; i < nc; i++) printf(" %04x(%d)", comp[i], __builtin_popcount(comp[i])); printf("\n");
    return 0;
}
