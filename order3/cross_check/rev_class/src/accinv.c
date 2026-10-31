/* Referee harness: acceptance-rule invariance test for frames.c at n=24.
   For a code E (12 rows from a class key line), A(E) = set of weight-8 supports S that frames.c's acceptance would
   accept as e1 (max acc_key, nauty_choice for ties). Checks A(E) nonempty and A(g E) = g A(E) for random
   g in Mon x conj.  Includes frames.c verbatim (main renamed). */
#define main frames_main
#include "frames.c"
#undef main
static uint32_t sup[4096]; static int nsup;
static void scb2(f4v w, int nrows, void *c) {
    if (f4wt(w) != 8) return;
    uint32_t s = f4supp(w);
    for (int i = 0; i < nsup; i++) if (sup[i] == s) return;
    sup[nsup++] = s;
}
/* returns |A|, fills Aset (sorted) */
static int accset(const f4v *gen, uint32_t *Aset, int *nties) {
    nsup = 0; sd_lowwords(gen, 24, 8, scb2, NULL);
    uint64_t best = 0; int first = 1;
    for (int i = 0; i < nsup; i++) { uint64_t k = acc_key(sup, nsup, i, NULL); if (first || k > best) { best = k; first = 0; } }
    uint32_t tied[4096]; int nt = 0;
    for (int i = 0; i < nsup; i++) if (acc_key(sup, nsup, i, NULL) == best) tied[nt++] = sup[i];
    *nties = nt;
    int na = 0;
    if (nt == 1) { Aset[na++] = tied[0]; }
    else for (int t = 0; t < nt; t++) if (nauty_choice(gen, tied[t], tied, nt)) Aset[na++] = tied[t];
    qsort(Aset, na, 4, cmpu);
    return na;
}
static f4v applyg(f4v x, const int *perm, const int *sc, int cj) {
    f4v y = { 0, 0 };
    for (int i = 0; i < 24; i++) { int e = f4get(x, i); if (!e) continue; if (cj) e = F4CONJ[e]; f4set(&y, perm[i], F4MUL[e][sc[i]]); }
    return y;
}
int main(int argc, char **argv) {
    n = 24; d = 8; nb = 16; kb = 5; m = 6;
    rng_t R; rng_seed(&R, argc > 2 ? atoll(argv[2]) : 12345);
    int ntrials = argc > 3 ? atoi(argv[3]) : 2;
    FILE *f = fopen(argv[1], "r"); char line[8192]; long nc = 0, nfail = 0, nempty = 0;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12];
        for (int r = 0; r < 12; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        char *p = line + 192; long aut = 0; int a8 = 0, sc = 0; sscanf(p, "%ld %d %d", &aut, &a8, &sc);
        uint32_t A0[4096], A1[4096], gA[4096]; int nt0, nt1;
        int na0 = accset(gen, A0, &nt0);
        if (na0 == 0) nempty++;
        int bad = 0;
        if (3 * nsup != a8) { printf("A8 mismatch %d vs %d\n", 3 * nsup, a8); bad = 1; }
        for (int tr = 0; tr < ntrials; tr++) {
            int perm[24], scl[24], cj = (int)(rng_next(&R) & 1);
            for (int i = 0; i < 24; i++) perm[i] = i;
            for (int i = 23; i > 0; i--) { int j = rng_next(&R) % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
            for (int i = 0; i < 24; i++) scl[i] = 1 + rng_next(&R) % 3;
            f4v g2[12]; for (int r = 0; r < 12; r++) g2[r] = applyg(gen[r], perm, scl, cj);
            /* random row mixing to avoid identical generator shapes */
            for (int r = 0; r < 12; r++) for (int s = 0; s < 12; s++) if (r != s && (rng_next(&R) & 3) == 0) g2[r] = f4add(g2[r], f4smul(1 + rng_next(&R) % 3, g2[s]));
            if (f4rank(g2, 12, 24) != 12) { tr--; continue; }
            int na1 = accset(g2, A1, &nt1);
            for (int i = 0; i < na0; i++) { uint32_t s = 0; for (uint32_t mm = A0[i]; mm; mm &= mm - 1) s |= 1u << perm[__builtin_ctz(mm)]; gA[i] = s; }
            qsort(gA, na0, 4, cmpu);
            if (na1 != na0 || memcmp(gA, A1, 4 * na0) || nt1 != nt0) bad = 1;
        }
        nc++; if (bad) nfail++;
        printf("code %ld aut %ld sc %d A8 %d ties %d |A| %d %s\n", nc, aut, sc, a8, nt0, na0, bad ? "FAIL" : "ok");
        fflush(stdout);
    }
    printf("SUMMARY codes %ld fail %ld emptyA %ld\n", nc, nfail, nempty);
    return 0;
}
