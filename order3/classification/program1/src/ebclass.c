/* Classification of Hermitian self-orthogonal [nb, k, >= d] codes over F4 up to monomial equivalence and
   conjugation, k = 1 .. kmax, by extension: a (k+1)-dim code C' contains a k-dim subcode C, C' = C + <x> with
   x in C^perp, <x,x> = 0, min weight of x + C >= d.  Extensions of a representative C are taken up to Aut(C)
   (union-find over the cosets C^perp / C, generators from nauty) and deduplicated by canonical class keys.
   Level 1 -> 2 is done by hand: C = <1^w>, Aut(C) = S_w x (monomial on the rest) x <global scalar on supp>, so
   x mod C is determined up to Aut(C) and scalars by the value counts on supp(1^w) modulo x -> lambda x + mu and
   the weight on the complement.
   Usage: ebclass nb kmax d infile|- outprefix [slice nslices]
     infile '-' : start from level 1; otherwise read level-k representatives (one per line: k then rows hex
     %08x%08x) and extend them by one level (only reps with index % nslices == slice).
   Output: outprefix.L<k+1>.txt lines: key(hex rows) |Aut| generator(hex rows).                          */
#include "cform.h"

static int nb, kmax, dmin;
/* ---------- automorphism generators via nauty ---------- */
static int ngens; static int (*gperm)[32]; static int (*gscal)[32];
static int g_ncoord;
static void autom_cb(int count, int *perm, int *orbits, int numorbits, int stabvertex, int n) {
    gperm = realloc(gperm, sizeof(int[32]) * (ngens + 1)); gscal = realloc(gscal, sizeof(int[32]) * (ngens + 1));
    for (int i = 0; i < g_ncoord; i++) {
        int v = perm[3 * i];                      /* image of X(i,0) = X(sigma i, s_i) */
        gperm[ngens][i] = v / 3; gscal[ngens][i] = v % 3;
    }
    ngens++;
}
static double code_aut_gens(const f4v *gen, int k, int n) {
    wlist_t L = { 0, 0, 0 }; wsel_t s = { &L, 1, n }; all_words(gen, k, wsel_cb, &s);
    int nw = L.n, nv = 3 * n + nw;
    size_t ne = 3 * n; for (int j = 0; j < nw; j++) ne += 2 * (size_t)f4wt(L.w[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "autgens"); sg.nv = nv; sg.nde = ne;
    int *deg = calloc(nv, sizeof(int));
    for (int i = 0; i < 3 * n; i++) deg[i] = 1;
    for (int j = 0; j < nw; j++) { uint32_t m = f4supp(L.w[j]); deg[3 * n + j] = __builtin_popcount(m); for (; m; m &= m - 1) { int i = __builtin_ctz(m); deg[3 * i + F4LOG[f4get(L.w[j], i)]]++; } }
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int a = 0; a < 3; a++) { int v = 3 * i + a; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + (a + 1) % 3; }
    for (int j = 0; j < nw; j++) { int y = 3 * n + j; for (uint32_t m = f4supp(L.w[j]); m; m &= m - 1) { int i = __builtin_ctz(m), x = 3 * i + F4LOG[f4get(L.w[j], i)]; sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y; } }
    free(deg);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    for (int v = 0; v < nv; v++) { lab[v] = v; ptn[v] = 1; }
    ptn[3 * n - 1] = 0; ptn[nv - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt);
    opt.getcanon = FALSE; opt.defaultptn = FALSE; opt.userautomproc = autom_cb;
    statsblk st;
    ngens = 0; g_ncoord = n;
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, NULL);
    free(lab); free(ptn); free(orb); free(L.w); SG_FREE(sg);
    return st.grpsize1 * pow(10.0, st.grpsize2);
}
static f4v apply_mono(int g, f4v x, int n) {
    f4v y = { 0, 0 };
    for (int i = 0; i < n; i++) { int e = f4get(x, i); if (e) f4set(&y, gperm[g][i], F4MUL[e][F4EXP[gscal[g][i]]]); }
    return y;
}
/* ---------- class store ---------- */
typedef struct { f4v key[8]; f4v gen[8]; double aut; int sc; } cls_t;
static cls_t *cls; static long ncls, capcls;
static long *htab; static long hcap;
static int kcur;    /* dimension of stored classes */
static long find_or_add(const f4v *key, const f4v *gen, double aut, int sc) {
    if (!htab) { hcap = 1 << 20; htab = malloc(sizeof(long) * hcap); for (long i = 0; i < hcap; i++) htab[i] = -1; }
    if (2 * ncls >= hcap) {
        long nc = hcap * 2; long *nt = malloc(sizeof(long) * nc); for (long i = 0; i < nc; i++) nt[i] = -1;
        for (long c = 0; c < ncls; c++) { uint64_t h = mat_hash(cls[c].key, kcur) & (nc - 1); while (nt[h] >= 0) h = (h + 1) & (nc - 1); nt[h] = c; }
        free(htab); htab = nt; hcap = nc;
    }
    uint64_t h = mat_hash(key, kcur) & (hcap - 1);
    while (htab[h] >= 0) { if (!mat_cmp(cls[htab[h]].key, key, kcur)) return htab[h]; h = (h + 1) & (hcap - 1); }
    if (ncls == capcls) { capcls = capcls ? 2 * capcls : 1024; cls = realloc(cls, sizeof(cls_t) * capcls); }
    memcpy(cls[ncls].key, key, sizeof(f4v) * kcur); memcpy(cls[ncls].gen, gen, sizeof(f4v) * kcur); cls[ncls].aut = aut; cls[ncls].sc = sc;
    htab[h] = ncls;
    return ncls++;
}
static long ncanon;
static void add_code(const f4v *gen, int k) {
    f4v key[8]; double az; int sc;
    if (canon_class(gen, k, nb, 1, key, &az, &sc)) { fprintf(stderr, "canon failed\n"); exit(1); }
    ncanon++;
    find_or_add(key, gen, az, sc);
}
/* ---------- level 1 -> 2 by value-count types ---------- */
static void level12(void) {
    kcur = 2;
    for (int w = dmin; w <= nb; w += 2) {
        f4v c1 = { 0, 0 }; for (int i = 0; i < w; i++) f4set(&c1, i, 1);
        for (int n0 = 0; n0 <= w; n0++) for (int n1 = 0; n0 + n1 <= w; n1++) for (int n2 = 0; n0 + n1 + n2 <= w; n2++) {
            int n3 = w - n0 - n1 - n2;
            if ((n1 & 1) != (n2 & 1) || (n2 & 1) != (n3 & 1)) continue;      /* Hermitian-orthogonal to 1^w */
            int mx = n0; if (n1 > mx) mx = n1; if (n2 > mx) mx = n2; if (n3 > mx) mx = n3;
            for (int u = 0; u <= nb - w; u++) {
                if ((w - n0 + u) & 1) continue;                                /* isotropic */
                if (u + w - mx < dmin) continue;                               /* min weight of x + C */
                f4v x = { 0, 0 }; int p = 0;
                for (int t = 0; t < n1; t++) f4set(&x, p++, 1);
                for (int t = 0; t < n2; t++) f4set(&x, p++, 2);
                for (int t = 0; t < n3; t++) f4set(&x, p++, 3);
                p = w; for (int t = 0; t < u; t++) f4set(&x, p++, 1);
                if (f4wt(x) == 0) continue;
                f4v g[2] = { c1, x };
                if (f4rank(g, 2, nb) < 2) continue;
                add_code(g, 2);
            }
        }
    }
}
/* ---------- general level k -> k+1 ---------- */
static int *uf;
static int uf_find(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static void uf_union(int a, int b) { a = uf_find(a); b = uf_find(b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }
static void extend_rep(const f4v *Cg, int k) {
    f4v C[8]; memcpy(C, Cg, sizeof(f4v) * k);
    int pc[8]; f4rref(C, k, nb, pc, NULL);
    f4v D[32]; int dd = f4hermdual(C, k, nb, D);              /* C^perp, dim nb - k */
    /* reduce D by C at pivots, then RREF the result: W basis (m = nb - 2k vectors) */
    f4v R[32]; int nr = 0;
    for (int i = 0; i < dd; i++) {
        f4v x = D[i];
        for (int j = 0; j < k; j++) { int e = f4get(x, pc[j]); if (e) x = f4add(x, f4smul(e, C[j])); }
        R[nr++] = x;
    }
    int pw[32]; int m = f4rref(R, nr, nb, pw, NULL);
    if (m != nb - 2 * k) { fprintf(stderr, "dim mismatch m=%d\n", m); exit(1); }
    int ncos = 1 << (2 * m);
    /* words of C */
    int nwc = 1 << (2 * k); f4v *cw = malloc(sizeof(f4v) * nwc);
    for (int t = 0; t < nwc; t++) { f4v x = { 0, 0 }; for (int j = 0; j < k; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, C[j])); cw[t] = x; }
    code_aut_gens(C, k, nb);
    uf = realloc(uf, sizeof(int) * ncos);
    for (int v = 0; v < ncos; v++) uf[v] = v;
    if (getenv("CHECKGENS")) {
        for (int g = 0; g < ngens; g++) for (int t = 0; t < nwc; t++) {
            f4v y = apply_mono(g, cw[t], nb); int found = 0;
            for (int u = 0; u < nwc; u++) if (f4eq(y, cw[u])) { found = 1; break; }
            if (!found) { fprintf(stderr, "generator %d does not preserve C\n", g); exit(1); }
        }
    }
    if (getenv("NOUF")) ngens = 0;
    for (int v = 0; v < ncos; v++) {
        f4v x = { 0, 0 }; for (int j = 0; j < m; j++) x = f4add(x, f4smul((v >> (2 * j)) & 3, R[j]));
        for (int g = 0; g < ngens; g++) {
            f4v y = apply_mono(g, x, nb);
            for (int j = 0; j < k; j++) { int e = f4get(y, pc[j]); if (e) y = f4add(y, f4smul(e, C[j])); }
            int u = 0; for (int j = 0; j < m; j++) u |= f4get(y, pw[j]) << (2 * j);
            uf_union(v, u);
        }
    }
    kcur = k + 1;
    for (int v = 1; v < ncos; v++) {
        if (uf_find(v) != v) continue;
        f4v x = { 0, 0 }; for (int j = 0; j < m; j++) x = f4add(x, f4smul((v >> (2 * j)) & 3, R[j]));
        if (f4wt(x) & 1) continue;                                     /* isotropic iff even weight */
        int ok = 1;
        for (int t = 0; t < nwc && ok; t++) if (f4wt(f4add(x, cw[t])) < dmin) ok = 0;
        if (!ok) continue;
        f4v g[8]; memcpy(g, C, sizeof(f4v) * k); g[k] = x;
        add_code(g, k + 1);
    }
    free(cw);
}
static void write_level(const char *prefix, int k) {
    char fn[512]; snprintf(fn, sizeof fn, "%s.L%d.txt", prefix, k);
    FILE *f = fopen(fn, "w");
    for (long c = 0; c < ncls; c++) {
        fprintf(f, "%d ", k);
        for (int r = 0; r < k; r++) fprintf(f, "%08x%08x", cls[c].key[r].a, cls[c].key[r].b);
        fprintf(f, " %.0f%s ", cls[c].aut, cls[c].sc ? "" : "x2");
        for (int r = 0; r < k; r++) fprintf(f, "%08x%08x", cls[c].gen[r].a, cls[c].gen[r].b);
        fprintf(f, "\n");
    }
    fclose(f);
}
int main(int argc, char **argv) {
    nb = atoi(argv[1]); kmax = atoi(argv[2]); dmin = atoi(argv[3]);
    const char *in = argv[4], *prefix = argv[5];
    int slice = argc > 6 ? atoi(argv[6]) : 0, nsl = argc > 7 ? atoi(argv[7]) : 1;
    if (!strcmp(in, "-")) {
        level12();
        fprintf(stderr, "level 2: %ld classes (%ld canonical forms)\n", ncls, ncanon);
        write_level(prefix, 2);
        return 0;
    }
    FILE *f = fopen(in, "r"); char line[4096]; long idx = 0; int k = 0;
    while (fgets(line, sizeof line, f)) {
        k = atoi(line);
        if (idx++ % nsl != slice) continue;
        /* skip key, read |Aut|, generator */
        char *p = strchr(line, ' ') + 1; p = strchr(p, ' ') + 1; p = strchr(p, ' ') + 1;
        f4v g[8];
        for (int r = 0; r < k; r++) { char t[9]; memcpy(t, p + 16 * r, 8); t[8] = 0; g[r].a = strtoul(t, 0, 16); memcpy(t, p + 16 * r + 8, 8); g[r].b = strtoul(t, 0, 16); }
        extend_rep(g, k);
    }
    fprintf(stderr, "level %d: %ld classes (%ld canonical forms) [slice %d/%d]\n", k + 1, ncls, ncanon, slice, nsl);
    write_level(prefix, k + 1);
    return 0;
}
