/* Referee: bordered double circulant Hermitian self-dual [24,12,8] codes [I_12 | B],
   B = [[alpha, beta 1^11], [gamma 1^11^T, A]], A 11x11 circulant over F4, B B^H = I.  Prints class keys. */
#include "cform.h"
static int bad;
static void lw(f4v w, int nr, void *c) { if (f4wt(w) < 8) bad = 1; }
int main(void) {
    long nsd = 0, nd8 = 0;
    for (uint32_t t = 0; t < (1u << 22); t++) {
        f4v a = { 0, 0 }; for (int i = 0; i < 11; i++) f4set(&a, i, (t >> (2 * i)) & 3);
        f4v sh[11];
        for (int s = 0; s < 11; s++) { f4v r = { 0, 0 }; for (int i = 0; i < 11; i++) f4set(&r, (i + s) % 11, f4get(a, i)); sh[s] = r; }
        /* circulant part: <sh0, shs> must be equal to gamma conj gamma (s != 0) and 1 + that (s = 0) */
        int c0 = f4herm(sh[0], sh[0]), cs = f4herm(sh[0], sh[1]), okc = 1;
        for (int s = 2; s < 11 && okc; s++) if (f4herm(sh[0], sh[s]) != cs) okc = 0;
        if (!okc) continue;
        int sa = 0; for (int i = 0; i < 11; i++) sa ^= F4CONJ[f4get(a, i)];       /* sum conj(a_k) */
        for (int g = 0; g < 4; g++) {
            int gg = g ? 1 : 0;                       /* gamma conj gamma */
            if (cs != gg) continue;
            if ((c0 ^ gg) != 1) continue;
            for (int al = 0; al < 4; al++) for (int be = 0; be < 4; be++) {
                int n0 = (al ? 1 : 0) ^ (be ? 1 : 0);  /* 11 beta conj beta = [beta != 0] */
                if (n0 != 1) continue;
                if ((F4MUL[al][F4CONJ[g]] ^ F4MUL[be][sa]) != 0) continue;
                nsd++;
                f4v gen[12];
                f4v r0 = { 0, 0 }; f4set(&r0, 0, 1); f4set(&r0, 12, al); for (int i = 0; i < 11; i++) f4set(&r0, 13 + i, be);
                gen[0] = r0;
                for (int s = 0; s < 11; s++) { f4v x = { 0, 0 }; f4set(&x, 1 + s, 1); f4set(&x, 12, g); for (int i = 0; i < 11; i++) f4set(&x, 13 + i, f4get(sh[s], i)); gen[1 + s] = x; }
                /* verify self-orthogonality directly */
                int so = 1; for (int i = 0; i < 12 && so; i++) for (int j = i; j < 12 && so; j++) if (f4herm(gen[i], gen[j])) so = 0;
                if (!so) { fprintf(stderr, "not s.o.?\n"); continue; }
                bad = 0; sd_lowwords(gen, 24, 7, lw, NULL);
                if (bad) continue;
                nd8++;
                f4v key[16]; double az; int sc;
                if (canon_class(gen, 12, 24, 8, key, &az, &sc)) { fprintf(stderr, "canon fail\n"); return 1; }
                for (int r = 0; r < 12; r++) printf("%08x%08x", key[r].a, key[r].b);
                printf(" %.0f %d\n", az, sc);
            }
        }
    }
    fprintf(stderr, "self-dual bordered double circulant: %ld, d>=8: %ld\n", nsd, nd8);
    return 0;
}
