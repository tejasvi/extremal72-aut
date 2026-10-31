/* Auditor test (rev_reclass): invariance of the class key (cform canon_class via ckey.c, and own mycanon2
   word-list key) under random monomial maps + conjugation, and independent check of cls24 records
   (self-duality, rank 12, d = 8, A8 by full enumeration, key reproduces itself, aut/sc).
   Input lines: KEY(12 rows hex %08x%08x) aut A8 sc ...
   usage: cinv FILE NTRANS SEED */
#include "mycanon2.h"
int c3c_class_key(const unsigned *lo, const unsigned *hi, int k, int n, int d, unsigned *klo, unsigned *khi,
                  double *aut, int *sc);
static u64 st = 88172645463325252ULL;
static u64 rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }
static int herm24(vec a, vec b) { return vherm(a, b); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int ntr = atoi(argv[2]); st ^= (u64)atol(argv[3]) * 0x9E3779B97F4A7C15ULL;
    char line[8192]; long nl = 0, bad = 0, badrec = 0, nonspan = 0;
    while (fgets(line, sizeof line, f)) {
        vec g[12]; char *q = line;
        for (int r = 0; r < 12; r++) { char h[9]; memcpy(h, q, 8); h[8] = 0; g[r].lo = strtoul(h, 0, 16); memcpy(h, q + 8, 8); h[8] = 0; g[r].hi = strtoul(h, 0, 16); q += 16; }
        double aut; long a8; int sc; if (sscanf(q, "%lf %ld %d", &aut, &a8, &sc) != 3) { fprintf(stderr, "parse\n"); return 2; }
        nl++;
        /* independent record check */
        vec tmp[12]; memcpy(tmp, g, sizeof tmp); int pv[16]; int rk = vrref(tmp, 12, 24, pv);
        int so = 1; for (int i = 0; i < 12; i++) for (int j = 0; j < 12; j++) if (herm24(g[i], g[j])) so = 0;
        vec B[24]; for (int i = 0; i < 12; i++) { B[2 * i] = g[i]; B[2 * i + 1] = vmulw(g[i]); }
        vec cur = {0, 0}; long cnt8 = 0, cntlow = 0; int minw = 99;
        vec *W8 = malloc(sizeof(vec) * (a8 + 16)); long nw8 = 0;
        for (u64 x = 1; x < (1ULL << 24); x++) { cur = vadd(cur, B[__builtin_ctzll(x)]); int w = vwt(cur); if (w < minw) minw = w; if (w < 8) cntlow++; if (w == 8) { if (nw8 < a8 + 16) W8[nw8] = cur; nw8++; cnt8++; } }
        if (rk != 12 || !so || minw != 8 || cnt8 != a8) { badrec++; fprintf(stderr, "RECORD MISMATCH line %ld: rk %d so %d minw %d A8 %ld vs %ld\n", nl, rk, so, minw, cnt8, a8); free(W8); continue; }
        unsigned lo[12], hi[12], klo[12], khi[12]; double ca; int csc;
        for (int i = 0; i < 12; i++) { lo[i] = g[i].lo; hi[i] = g[i].hi; }
        if (c3c_class_key(lo, hi, 12, 24, 8, klo, khi, &ca, &csc)) { fprintf(stderr, "cform failed\n"); return 3; }
        int same = 1; for (int i = 0; i < 12; i++) if (klo[i] != lo[i] || khi[i] != hi[i]) same = 0;
        if (!same || ca != aut || csc != sc) { bad++; fprintf(stderr, "KEY NOT FIXED line %ld (same %d aut %.0f/%.0f sc %d/%d)\n", nl, same, ca, aut, csc, sc); }
        int spans = 1; { vec t2[64]; int r = 0; for (long j = 0; j < nw8 && r < 12; j++) { t2[r] = W8[j]; int pp[64]; vec t3[64]; memcpy(t3, t2, sizeof(vec) * (r + 1)); if (vrref(t3, r + 1, 24, pp) == r + 1) r++; } spans = (r == 12); }
        if (!spans) nonspan++;
        for (int t = 0; t < ntr; t++) {
            int perm[24]; for (int i = 0; i < 24; i++) perm[i] = i; for (int i = 23; i > 0; i--) { int j = rnd() % (i + 1); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
            int mu[24]; for (int i = 0; i < 24; i++) mu[i] = 1 + rnd() % 3; int cj = rnd() & 1;
            vec h[12]; for (int r = 0; r < 12; r++) { vec y = {0, 0}; for (int i = 0; i < 24; i++) { int c = vget(g[r], i); if (c) vset(&y, perm[i], f4mul[c][mu[i]]); } if (cj) y = mc_conjv(y); h[r] = y; }
            /* random basis change: add random combinations */
            for (int r = 0; r < 12; r++) for (int s = 0; s < 12; s++) if (r != s && (rnd() & 3) == 0) h[r] = vadd(h[r], vscal(1 + rnd() % 3, h[s]));
            vec hh[12]; memcpy(hh, h, sizeof hh); if (vrref(hh, 12, 24, pv) != 12) { memcpy(h, hh, sizeof h); }   /* keep full rank (combos may be dependent -> skip) */
            if (vrref(hh, 12, 24, pv) != 12) continue;
            unsigned l2[12], h2[12], k2l[12], k2h[12]; double a2; int s2;
            for (int i = 0; i < 12; i++) { l2[i] = h[i].lo; h2[i] = h[i].hi; }
            if (c3c_class_key(l2, h2, 12, 24, 8, k2l, k2h, &a2, &s2)) { fprintf(stderr, "cform failed 2\n"); return 3; }
            int eq = 1; for (int i = 0; i < 12; i++) if (k2l[i] != lo[i] || k2h[i] != hi[i]) eq = 0;
            /* own key from transformed code with its own weight-8 word list (or <= 10 if not spanning) */
            vec *L; long nL; { vec Bt[24]; for (int i = 0; i < 12; i++) { Bt[2 * i] = h[i]; Bt[2 * i + 1] = vmulw(h[i]); } long cap = 1 << 16; L = malloc(sizeof(vec) * cap); nL = 0; vec c2 = {0, 0};
                int wm = spans ? 8 : 10;
                for (;;) { nL = 0; c2.lo = c2.hi = 0; for (u64 x = 1; x < (1ULL << 24); x++) { c2 = vadd(c2, Bt[__builtin_ctzll(x)]); if (vwt(c2) <= wm) { if (nL == cap) { cap *= 2; L = realloc(L, sizeof(vec) * cap); } L[nL++] = c2; } }
                    vec t2[64]; int r = 0; for (long j = 0; j < nL && r < 12; j++) { t2[r] = L[j]; vec t3[64]; int pp[64]; memcpy(t3, t2, sizeof(vec) * (r + 1)); if (vrref(t3, r + 1, 24, pp) == r + 1) r++; }
                    if (r == 12) break; wm += 2; } }
            vec ok[16]; double oa; int osc; mc_class_wl(h, 12, 24, L, nL, ok, &oa, &osc); free(L);
            int eq2 = 1; for (int i = 0; i < 12; i++) if (ok[i].lo != lo[i] || ok[i].hi != hi[i]) eq2 = 0;
            if (!eq || a2 != aut || s2 != sc || !eq2 || oa != aut || osc != sc) { bad++; fprintf(stderr, "INVARIANCE FAIL line %ld trans %d (cform %d own %d)\n", nl, t, eq, eq2); }
        }
        free(W8);
    }
    printf("lines %ld record_mismatch %ld key_failures %ld nonspanning %ld\n", nl, badrec, bad, nonspan);
    return 0;
}
