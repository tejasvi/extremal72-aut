/* Referee harness: for codes E (cls24 key lines), compute E_B = E^{S}|_{S^c} for weight-8 supports S (all, or every
   'step'-th) and check that its Mon x conj class key is in the E_B level-5 list (field 2 of n24.L5.txt). */
#include "cform.h"
static f4v (*K5)[5]; static long nk5;
static int cmpk(const void *a, const void *b) { return mat_cmp((const f4v *)a, (const f4v *)b, 5); }
static uint32_t sup[4096]; static f4v supw[4096]; static int nsup;
static void scb(f4v w, int nr, void *c) {
    if (f4wt(w) != 8) return; uint32_t s = f4supp(w);
    for (int i = 0; i < nsup; i++) if (sup[i] == s) return;
    supw[nsup] = w; sup[nsup++] = s;
}
static void parse(const char *p, f4v *g, int k) { for (int r = 0; r < k; r++) { char t[9]; memcpy(t, p + 16 * r, 8); t[8] = 0; g[r].a = strtoul(t, 0, 16); memcpy(t, p + 16 * r + 8, 8); g[r].b = strtoul(t, 0, 16); } }
int main(int argc, char **argv) {
    int n = 24, d = 8, k = 12, kb = 5; int step = argc > 3 ? atoi(argv[3]) : 1;
    FILE *f = fopen(argv[1], "r"); char line[8192]; long cap = 50000; K5 = malloc(sizeof(f4v[5]) * cap);
    while (fgets(line, sizeof line, f)) { char *p = strchr(line, ' ') + 1; parse(p, K5[nk5], 5); nk5++; }
    fclose(f); qsort(K5, nk5, sizeof(f4v[5]), cmpk);
    fprintf(stderr, "loaded %ld E_B keys\n", nk5);
    f = fopen(argv[2], "r"); long nc = 0, nmiss = 0, nchk = 0;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12]; parse(line, gen, 12); nc++;
        nsup = 0; sd_lowwords(gen, n, d, scb, NULL);
        int miss = 0;
        for (int s = 0; s < nsup; s += step) {
            int pos[32], p = 0, sc[32];
            for (int i = 0; i < n; i++) if ((sup[s] >> i) & 1) { pos[i] = p++; sc[i] = F4INV[f4get(supw[s], i)]; }
            for (int i = 0; i < n; i++) if (!((sup[s] >> i) & 1)) { pos[i] = p++; sc[i] = 1; }
            f4v g2[12]; for (int r = 0; r < k; r++) { f4v x = { 0, 0 }; for (int i = 0; i < n; i++) { int e = f4get(gen[r], i); if (e) f4set(&x, pos[i], F4MUL[e][sc[i]]); } g2[r] = x; }
            int piv[32]; f4rref(g2, k, n, piv, NULL);
            f4v EB[12]; int neb = 0;
            for (int r = 0; r < k; r++) if (piv[r] >= d) { EB[neb].a = g2[r].a >> d; EB[neb].b = g2[r].b >> d; neb++; }
            if (neb != kb) { printf("code %ld support %d: E_B dim %d\n", nc, s, neb); miss++; continue; }
            f4v key[8]; double az; int scf;
            if (canon_class(EB, kb, 16, 1, key, &az, &scf)) { printf("canon fail\n"); exit(1); }
            nchk++;
            if (!bsearch(key, K5, nk5, sizeof(f4v[5]), cmpk)) { miss++; printf("MISSING E_B: code %ld support %08x aut %.0f sc %d key ", nc, sup[s], az, scf); for (int r = 0; r < 5; r++) printf("%08x%08x", key[r].a, key[r].b); printf("\n"); }
        }
        if (miss) nmiss++;
        if (nc % 200 == 0) { fprintf(stderr, "%ld codes, %ld E_B checked, %ld codes with missing\n", nc, nchk, nmiss); }
    }
    printf("SUMMARY codes %ld E_B-checked %ld codes-with-missing %ld\n", nc, nchk, nmiss);
    return 0;
}
