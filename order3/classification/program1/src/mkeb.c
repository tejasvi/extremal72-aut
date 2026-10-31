/* extract E_B = E^{S}|_{S^c} for the first weight-d support S of each sampled code (ebclass file format, key = gen) */
#include "cform.h"
static int n, d; typedef struct { uint32_t s; f4v w; int got; } first_t;
static void cb(f4v w, int nr, void *c) { first_t *F = (first_t *)c; if (f4wt(w) == d && !F->got) { F->s = f4supp(w); F->w = w; F->got = 1; } }
int main(int argc, char **argv) {
    n = atoi(argv[1]); d = atoi(argv[2]); int k = n / 2, kb = k - d + 1; long maxc = atol(argv[4]);
    FILE *f = fopen(argv[3], "r"); char line[8192]; long c = 0;
    while (c < maxc && fgets(line, sizeof line, f)) {
        f4v gen[12]; for (int r = 0; r < k; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        first_t F = { 0, { 0, 0 }, 0 }; sd_lowwords(gen, n, d, cb, &F);
        int pos[32], p = 0, sc[32];
        for (int i = 0; i < n; i++) if ((F.s >> i) & 1) { pos[i] = p++; sc[i] = F4INV[f4get(F.w, i)]; }
        for (int i = 0; i < n; i++) if (!((F.s >> i) & 1)) { pos[i] = p++; sc[i] = 1; }
        f4v g2[12]; for (int r = 0; r < k; r++) { f4v x = { 0, 0 }; for (int i = 0; i < n; i++) { int e = f4get(gen[r], i); if (e) f4set(&x, pos[i], F4MUL[e][sc[i]]); } g2[r] = x; }
        int piv[32]; f4rref(g2, k, n, piv, NULL);
        f4v EB[12]; int neb = 0;
        for (int r = 0; r < k; r++) if (piv[r] >= d) { EB[neb].a = g2[r].a >> d; EB[neb].b = g2[r].b >> d; neb++; }
        if (neb != kb) { fprintf(stderr, "dim %d\n", neb); continue; }
        printf("%d ", kb); for (int r = 0; r < kb; r++) printf("%08x%08x", EB[r].a, EB[r].b); printf(" 3 ");
        for (int r = 0; r < kb; r++) printf("%08x%08x", EB[r].a, EB[r].b); printf("\n");
        c++;
    }
    return 0;
}
