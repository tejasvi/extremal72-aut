/* E_B classification by level extension with Aut-orbit reduction and canonical dedupe (c3explore, independent
   of c3class).  Codes: Hermitian self-orthogonal [NB, k, >= DMIN] over F4; equivalence = monomial x conjugation.
   Level k -> k+1: for each level-k class representative C, the group Aut_Mon(C) (generators from nauty) acts on
   the cosets of C in C^perp (as matrices on C^perp / C); one representative per orbit of nonzero cosets that is
   isotropic and has minimum coset weight >= DMIN gives a child C + <v>, output with its class key.  Every class
   of dimension k+1 arises (its k-dim subcodes have d >= DMIN), and equivalent children come from the same orbit
   or from different parents/orbits, so dedupe of the output by key (sort -u) gives exactly the level-(k+1) classes.
   Output line: KEY aut selfconj fullsupp hall    (hall: matching conditions for the glue with e1 = 1^DG)
   Usage: ebcls2 NB DMIN DG 1 OUTFILE   |   ebcls2 NB DMIN DG LEV INFILE OUTFILE [PART NPARTS] */
#include "mycanon.h"
static int NB, DMIN, DG;
/* ---- automorphism generators via nauty userautomproc ---- */
#define MAXGENS 512
static int ngens, gen_pi[MAXGENS][32], gen_mu[MAXGENS][32], cap_n;
static void autom_cb(int count, int *perm, int *orbits, int numorbits, int stabvertex, int nn) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex; (void)nn;
    if (ngens >= MAXGENS) return;
    for (int i = 0; i < cap_n; i++) { int t = perm[3 * i]; gen_pi[ngens][i] = t / 3; gen_mu[ngens][i] = t % 3 + 1; }
    ngens++;
}
/* automorphism generators of the code (monomial maps): g(v)_{pi(i)} = mu_i v_i */
static void aut_gens(const vec *gen, int k, int n) {
    vec rows[16]; memcpy(rows, gen, sizeof(vec) * k); int piv[16]; int rk = vrref(rows, k, n, piv);
    long nw = 1; for (int i = 0; i < rk; i++) nw *= 4; nw -= 1;
    vec *all = malloc(sizeof(vec) * (nw + 1)); combos(rows, rk, all);
    int m = (int)nw, nv = 3 * n + m;
    size_t ne = 3 * n; for (int j = 1; j <= m; j++) ne += 2 * (size_t)vwt(all[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "aut_gens"); sg.nv = nv; sg.nde = ne;
    int *deg = calloc(nv, sizeof(int));
    for (int v = 0; v < 3 * n; v++) deg[v] = 1;
    for (int j = 1; j <= m; j++) { u32 s = vsupp(all[j]); deg[3 * n + j - 1] = __builtin_popcount(s); for (; s; s &= s - 1) { int i = __builtin_ctz(s); deg[3 * i + vget(all[j], i) - 1]++; } }
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int l = 1; l <= 3; l++) { int v = 3 * i + l - 1; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + f4mul[l][2] - 1; }
    for (int j = 1; j <= m; j++) { int y = 3 * n + j - 1; for (u32 s = vsupp(all[j]); s; s &= s - 1) { int i = __builtin_ctz(s); int x = 3 * i + vget(all[j], i) - 1; sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y; } }
    free(deg); free(all);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    for (int v = 0; v < nv; v++) { lab[v] = v; ptn[v] = 1; } ptn[3 * n - 1] = 0; ptn[nv - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt); opt.getcanon = FALSE; opt.defaultptn = FALSE; opt.userautomproc = autom_cb;
    statsblk st; ngens = 0; cap_n = n;
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, NULL);
    free(lab); free(ptn); free(orb); SG_FREE(sg);
}
static vec apply_mon(int g, vec v) { vec r = {0, 0}; for (int i = 0; i < NB; i++) { int c = vget(v, i); if (c) vset(&r, gen_pi[g][i], f4mul[c][gen_mu[g][i]]); } return r; }
/* ---- side class distribution and flags (Hall) ---- */
static long NS[40]; static int ns_done;
static void side_dist(void) {
    if (ns_done) return; ns_done = 1; int g = DG - 2; long tot = 1; for (int i = 0; i < g; i++) tot *= 4;
    vec ub[16]; for (int i = 0; i < g; i++) { ub[i].lo = (1u << i) | (1u << (DG - 2)); ub[i].hi = 0; } vec one = { (1u << DG) - 1, 0 };
    for (long idx = 1; idx < tot; idx++) { vec x = {0, 0}; long t = idx; for (int i = 0; i < g; i++) { int d = t & 3; t >>= 2; if (d) x = vadd(x, vscal(d, ub[i])); }
        int mw = 99; for (int l = 0; l < 4; l++) { int w = vwt(vadd(x, vscal(l, one))); if (w < mw) mw = w; } NS[mw]++; }
}
static int perp_complement(const vec *C, int k, vec *Wb) {
    vec c[16]; memcpy(c, C, sizeof(vec) * k); int pv[16]; vrref(c, k, NB, pv);
    u32 pm = 0; for (int i = 0; i < k; i++) pm |= 1u << pv[i];
    vec perp[32]; int np = 0;
    for (int j = 0; j < NB; j++) if (!((pm >> j) & 1)) { vec x = {0, 0}; vset(&x, j, 1); for (int i = 0; i < k; i++) vset(&x, pv[i], f4conj[vget(c[i], j)]); perp[np++] = x; }
    vec cur[32]; int nc = 0; for (int i = 0; i < k; i++) cur[nc++] = c[i];
    int nw = 0;
    for (int t = 0; t < np; t++) { vec tmp[32]; memcpy(tmp, cur, sizeof(vec) * nc); tmp[nc] = perp[t]; int pp[32]; if (vrref(tmp, nc + 1, NB, pp) == nc + 1) { cur[nc++] = perp[t]; Wb[nw++] = perp[t]; } }
    return nw;
}
static void flags(const vec *C, int k, int *fullsupp, int *hall) {
    static vec all[1 << 12]; combos(C, k, all); long nall = 1L << (2 * k);
    u32 sup = 0; for (long i = 0; i < nall; i++) sup |= vsupp(all[i]); *fullsupp = (sup == (1u << NB) - 1);
    vec Wb[32]; int nw = perp_complement(C, k, Wb); long ncos = 1L << (2 * nw); long NW[40] = {0};
    vec *cos = malloc(sizeof(vec) * ncos); combos(Wb, nw, cos);
    for (long c = 1; c < ncos; c++) { int mw = 99; for (long i = 0; i < nall; i++) { int w = vwt(vadd(cos[c], all[i])); if (w < mw) mw = w; } NW[mw]++; }
    free(cos); side_dist();
    int ok = 1;
    for (int t = 0; t <= 32 && ok; t++) { long a = 0, b = 0, c2 = 0, d2 = 0;
        for (int m = 1; m <= t; m++) { a += NW[m]; c2 += NS[m]; }
        for (int m = (DG - t > 1 ? DG - t : 1); m < 40; m++) { b += NS[m]; d2 += NW[m]; }
        if (a > b || c2 > d2) ok = 0; }
    *hall = ok;
}
/* decomposition of x in C^perp as coordinates over the basis B = [C; W] (m vectors): RREF with transform */
static int Bm; static vec Brref[32]; static int Bpiv[32]; static int Tm[32][32];     /* Brref = T * B */
static void decomp_init(const vec *B, int m) {
    Bm = m; vec R[32]; memcpy(R, B, sizeof(vec) * m);
    int T[32][32]; for (int a = 0; a < m; a++) for (int b = 0; b < m; b++) T[a][b] = (a == b);
    int r = 0;
    for (int col = 0; col < NB && r < m; col++) {
        int sel = -1; for (int i = r; i < m; i++) if (vget(R[i], col)) { sel = i; break; }
        if (sel < 0) continue;
        vec tv = R[sel]; R[sel] = R[r]; R[r] = tv; for (int b = 0; b < m; b++) { int t = T[sel][b]; T[sel][b] = T[r][b]; T[r][b] = t; }
        int inv = f4inv[vget(R[r], col)]; R[r] = vscal(inv, R[r]); for (int b = 0; b < m; b++) T[r][b] = f4mul[inv][T[r][b]];
        for (int i = 0; i < m; i++) if (i != r) { int c = vget(R[i], col); if (c) { R[i] = vadd(R[i], vscal(c, R[r])); for (int b = 0; b < m; b++) T[i][b] ^= f4mul[c][T[r][b]]; } }
        Bpiv[r++] = col;
    }
    memcpy(Brref, R, sizeof(vec) * m); memcpy(Tm, T, sizeof T);
}
static void decomp(vec x, int *coef) {   /* x = sum coef[b] B[b] */
    int cR[32]; for (int j = 0; j < Bm; j++) cR[j] = vget(x, Bpiv[j]);
    for (int b = 0; b < Bm; b++) { int s = 0; for (int j = 0; j < Bm; j++) if (cR[j]) s ^= f4mul[cR[j]][Tm[j][b]]; coef[b] = s; }
}
/* union-find */
static uint32_t *uf;
static uint32_t ufind(uint32_t a) { while (uf[a] != a) { uf[a] = uf[uf[a]]; a = uf[a]; } return a; }
static void uunion(uint32_t a, uint32_t b) { a = ufind(a); b = ufind(b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }
static void write_key(FILE *f, const vec *key, int k) { for (int r = 0; r < k; r++) fprintf(f, "%08x%08x", key[r].lo, key[r].hi); }
static int read_key(const char *s, vec *g) { int k = 0; while (s[16 * k] && s[16 * k] != ' ' && s[16 * k] != '\n') { char t[9]; memcpy(t, s + 16 * k, 8); t[8] = 0; g[k].lo = strtoul(t, 0, 16); memcpy(t, s + 16 * k + 8, 8); g[k].hi = strtoul(t, 0, 16); k++; } return k; }
int main(int argc, char **argv) {
    NB = atoi(argv[1]); DMIN = atoi(argv[2]); DG = atoi(argv[3]); int lev = atoi(argv[4]);
    if (lev == 1) {
        FILE *fo = fopen(argv[5], "w");
        for (int w = DMIN; w <= NB; w += 2) { vec g[1]; g[0].lo = (1u << w) - 1; g[0].hi = 0; vec key[1]; double aut; int sc; mc_class(g, 1, NB, key, &aut, &sc);
            int fs, h; flags(key, 1, &fs, &h); write_key(fo, key, 1); fprintf(fo, " %.0f %d %d %d\n", aut, sc, fs, h); }
        fclose(fo); return 0;
    }
    FILE *fi = fopen(argv[5], "r"), *fo = fopen(argv[6], "w");
    int part = argc > 8 ? atoi(argv[7]) : 0, nparts = argc > 8 ? atoi(argv[8]) : 1;
    char line[4096]; long li = 0, nchild = 0;
    while (fgets(line, sizeof line, fi)) {
        if (li++ % nparts != part) continue;
        vec C[16]; int k = read_key(line, C);
        if (k != lev - 1) { fprintf(stderr, "bad parent dimension\n"); return 2; }
        vec Wb[32]; int nw = perp_complement(C, k, Wb);
        vec B[32]; for (int i = 0; i < k; i++) B[i] = C[i]; for (int i = 0; i < nw; i++) B[k + i] = Wb[i];
        decomp_init(B, k + nw);
        aut_gens(C, k, NB);
        /* matrices of generators on C^perp / C: rows = images of W basis vectors, bit-sliced over nw digits */
        uint32_t nidx = 1u << (2 * nw);
        uf = malloc(sizeof(uint32_t) * nidx); for (uint32_t i = 0; i < nidx; i++) uf[i] = i;
        int nch = (nw + 3) / 4;
        static uint32_t tab[MAXGENS][4][256];
        for (int g = 0; g < ngens; g++) {
            uint32_t rowimg[16];
            for (int t = 0; t < nw; t++) { vec x = apply_mon(g, Wb[t]); int coef[32]; decomp(x, coef);
                uint32_t idx = 0; for (int s = 0; s < nw; s++) idx |= (uint32_t)coef[k + s] << (2 * s); rowimg[t] = idx; }
            /* image of index a = sum_t a_t * rowimg[t] (F4 combination, digits as 2-bit codes) */
            for (int ch = 0; ch < nch; ch++) for (int byte = 0; byte < 256; byte++) {
                vec acc = {0, 0};
                for (int d = 0; d < 4; d++) { int t = 4 * ch + d; if (t >= nw) break; int a = (byte >> (2 * d)) & 3; if (!a) continue;
                    vec rv = {0, 0}; for (int s = 0; s < nw; s++) vset(&rv, s, (rowimg[t] >> (2 * s)) & 3); acc = vadd(acc, vscal(a, rv)); }
                uint32_t idx = 0; for (int s = 0; s < nw; s++) idx |= (uint32_t)vget(acc, s) << (2 * s);
                tab[g][ch][byte] = idx;
            }
        }
        for (int g = 0; g < ngens; g++) for (uint32_t a = 1; a < nidx; a++) {
            uint32_t b = 0; for (int ch = 0; ch < nch; ch++) b ^= tab[g][ch][(a >> (8 * ch)) & 255];
            if (b != a) uunion(a, b);
        }
        static vec all[1 << 12]; combos(C, k, all); long nall = 1L << (2 * k);
        long norb = 0, nval = 0;
        for (uint32_t a = 1; a < nidx; a++) {
            if (ufind(a) != a) continue;       /* roots are the smallest members (union keeps the smaller root) */
            norb++;
            vec v = {0, 0}; for (int s = 0; s < nw; s++) { int d = (a >> (2 * s)) & 3; if (d) v = vadd(v, vscal(d, Wb[s])); }
            if (vwt(v) & 1) continue;
            int ok = 1; for (long i = 0; i < nall && ok; i++) if (vwt(vadd(v, all[i])) < DMIN) ok = 0;
            if (!ok) continue;
            nval++;
            vec g2[16]; memcpy(g2, C, sizeof(vec) * k); g2[k] = v;
            vec key[16]; double aut; int sc; mc_class(g2, k + 1, NB, key, &aut, &sc);
            int fs = 0, h = 0; flags(key, k + 1, &fs, &h);
            write_key(fo, key, k + 1); fprintf(fo, " %.0f %d %d %d\n", aut, sc, fs, h); nchild++;
        }
        free(uf);
        fprintf(stderr, "parent %ld: gens %d cosets %u orbits %ld valid %ld\n", li - 1, ngens, nidx, norb, nval);
    }
    fclose(fo); fprintf(stderr, "part %d/%d: %ld children\n", part, nparts, nchild);
    return 0;
}
