/* Referee: pure double circulant Hermitian self-dual [24,12,8] codes [I | A], A circulant over F4 with A A^H = I.
   Prints class key (cform.h canon_class) and |Aut_Mon| for each code with d >= 8. */
#include "cform.h"
static int bad;
static void lw(f4v w, int nr, void *c) { if (f4wt(w) < 8) bad = 1; }
int main(void) {
    long nsd = 0, nd8 = 0;
    for (uint32_t t = 0; t < (1u << 24); t++) {
        f4v a = { 0, 0 }; for (int i = 0; i < 12; i++) f4set(&a, i, (t >> (2 * i)) & 3);
        if (!(f4wt(a) & 1)) continue;
        f4v row[12];
        for (int s = 0; s < 12; s++) { f4v r = { 0, 0 }; for (int i = 0; i < 12; i++) f4set(&r, (i + s) % 12, f4get(a, i)); row[s] = r; }
        int ok = 1; for (int s = 1; s < 12 && ok; s++) if (f4herm(row[0], row[s])) ok = 0;
        if (!ok) continue;
        nsd++;
        f4v gen[12]; for (int s = 0; s < 12; s++) { f4v g = { 0, 0 }; f4set(&g, s, 1); g.a |= row[s].a << 12; g.b |= row[s].b << 12; gen[s] = g; }
        bad = 0; sd_lowwords(gen, 24, 7, lw, NULL);
        if (bad) continue;
        nd8++;
        f4v key[16]; double az; int sc;
        if (canon_class(gen, 12, 24, 8, key, &az, &sc)) { fprintf(stderr, "canon fail\n"); return 1; }
        for (int r = 0; r < 12; r++) printf("%08x%08x", key[r].a, key[r].b);
        printf(" %.0f %d\n", az, sc);
    }
    fprintf(stderr, "self-dual double circulant: %ld, d>=8: %ld\n", nsd, nd8);
    return 0;
}
