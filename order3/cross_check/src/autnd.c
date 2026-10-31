/* autnd.c -- |Aut_Mon(E)| and Mon-equivalence of E and conj(E) via nauty on an OWN graph encoding:
   vertices: 24 coordinate vertices (colour 0); 3 value vertices per coordinate (colour 1); one vertex per nonzero
   word of the spanning word set (all scalar multiples; colour 2 for weight 8, 3 for weight 10); the scalar action
   w -> w*omega is encoded by a subdivided arc w - t - h - (w*omega) with t (colour 4) and h (colour 5).
   Graph automorphisms = monomial maps preserving the word set (= Aut_Mon(E) when the set spans E).
   Input: lines "... | <cls24 line>" or plain cls24 lines; output: idx autfield scfield myaut myselfconj nwords */
#include "lowwords.h"
#include "nauty.h"
#include "nausparse.h"
#include <math.h>

typedef struct { int nv; int ne; int *deg; int **adj; int *col; } G;
static int print_gens = 0;
static void ugen(int count, int *perm, int *orbits, int numorbits, int stabvertex, int n) {
    (void)count; (void)orbits; (void)numorbits; (void)stabvertex; (void)n;
    if (!print_gens) return;
    printf("GEN"); for (int i = 0; i < 24; i++) printf(" %d", perm[i]); printf("\n");
}

static int build(const v24 *rows, int conjflag, sparsegraph *sg, int **labp, int **ptnp, int *nwords, int *rank8) {
    v24 r[12]; for (int t = 0; t < 12; t++) r[t] = conjflag ? vconj(rows[t]) : rows[t];
    wlist L8 = { 0, 0, NULL }, L10 = { 0, 0, NULL };
    if (lowwords(r, 8, 8, &L8) != 0) return -1;
    /* rank of weight-8 words */
    v24 b[24]; int pv[24], rk = 0;
    for (int j = 0; j < L8.n && rk < 12; j++) {
        v24 y = L8.w[j];
        for (int t = 0; t < rk; t++) { int s = vget(y, pv[t]); if (s) y = vadd(y, vscal(b[t], s)); }
        if (viszero(y)) continue;
        int c = __builtin_ctz(vsupp(y)); y = vscal(y, F4INV[vget(y, c)]);
        for (int t = 0; t < rk; t++) { int s = vget(b[t], c); if (s) b[t] = vadd(b[t], vscal(y, s)); }
        b[rk] = y; pv[rk] = c; rk++;
    }
    *rank8 = rk;
    if (rk < 12) { if (lowwords(r, 10, 10, &L10) != 0) return -1; }
    int nw = L8.n + L10.n;
    *nwords = nw;
    v24 *W = malloc(sizeof(v24) * (size_t)nw);
    memcpy(W, L8.w, sizeof(v24) * (size_t)L8.n);
    if (L10.n) memcpy(W + L8.n, L10.w, sizeof(v24) * (size_t)L10.n);
    /* index words for the omega map: sort-free lookup by hashing */
    int hsz = 1; while (hsz < 4 * nw) hsz <<= 1;
    int *ht = malloc(sizeof(int) * (size_t)hsz); for (int i = 0; i < hsz; i++) ht[i] = -1;
    for (int j = 0; j < nw; j++) { uint64_t k = ((uint64_t)W[j].a << 32) | W[j].b; int h = (int)(smix(k) & (uint64_t)(hsz - 1)); while (ht[h] >= 0) h = (h + 1) & (hsz - 1); ht[h] = j; }
    int *om = malloc(sizeof(int) * (size_t)nw);
    for (int j = 0; j < nw; j++) {
        v24 x = vmulw(W[j]); uint64_t k = ((uint64_t)x.a << 32) | x.b; int h = (int)(smix(k) & (uint64_t)(hsz - 1));
        om[j] = -1; while (ht[h] >= 0) { if (W[ht[h]].a == x.a && W[ht[h]].b == x.b) { om[j] = ht[h]; break; } h = (h + 1) & (hsz - 1); }
        if (om[j] < 0) { fprintf(stderr, "omega image missing\n"); exit(2); }
    }
    int nv = 24 + 72 + nw + 2 * nw;
    /* degrees */
    int *deg = calloc((size_t)nv, sizeof(int));
    for (int i = 0; i < 24; i++) deg[i] = 3;
    for (int j = 0; j < nw; j++) {
        int wv = 96 + j, tv = 96 + nw + j, hv = 96 + 2 * nw + j;
        deg[wv] += vwt(W[j]) + 2;    /* values + its tail + head of the arc into it */
        deg[tv] = 2; deg[hv] = 2;
        for (uint32_t s = vsupp(W[j]); s; s &= s - 1) { int i = __builtin_ctz(s); deg[24 + 3 * i + vget(W[j], i) - 1]++; }
    }
    for (int i = 0; i < 24; i++) for (int s = 0; s < 3; s++) deg[24 + 3 * i + s]++;   /* edge to coordinate */
    size_t ne = 0; for (int v = 0; v < nv; v++) ne += (size_t)deg[v];
    SG_INIT(*sg);
    SG_ALLOC(*sg, nv, ne, "sg");
    sg->nv = nv; sg->nde = ne;
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg->v[v] = pos; sg->d[v] = 0; pos += (size_t)deg[v]; }
#define ADDE(x, y) do { sg->e[sg->v[x] + sg->d[x]++] = (y); sg->e[sg->v[y] + sg->d[y]++] = (x); } while (0)
    for (int i = 0; i < 24; i++) for (int s = 0; s < 3; s++) ADDE(i, 24 + 3 * i + s);
    for (int j = 0; j < nw; j++) {
        int wv = 96 + j, tv = 96 + nw + j, hv = 96 + 2 * nw + j;
        for (uint32_t s = vsupp(W[j]); s; s &= s - 1) { int i = __builtin_ctz(s); ADDE(wv, 24 + 3 * i + vget(W[j], i) - 1); }
        ADDE(wv, tv); ADDE(tv, hv); ADDE(hv, 96 + om[j]);
    }
    for (int v = 0; v < nv; v++) if (sg->d[v] != deg[v]) { fprintf(stderr, "degree mismatch %d\n", v); exit(3); }
    /* colours: 0 coords, 1 values, 2 wt8 words, 3 wt10 words, 4 tails, 5 heads */
    int *lab = malloc(sizeof(int) * (size_t)nv), *ptn = malloc(sizeof(int) * (size_t)nv);
    int k = 0;
    int cstart[7];
    for (int c = 0; c < 6; c++) {
        cstart[c] = k;
        for (int v = 0; v < nv; v++) {
            int cv;
            if (v < 24) cv = 0; else if (v < 96) cv = 1; else if (v < 96 + nw) cv = (v - 96 < L8.n) ? 2 : 3;
            else if (v < 96 + 2 * nw) cv = 4; else cv = 5;
            if (cv == c) lab[k++] = v;
        }
    }
    cstart[6] = k;
    for (int i = 0; i < nv; i++) ptn[i] = 1;
    for (int c = 0; c < 6; c++) if (cstart[c + 1] > cstart[c]) ptn[cstart[c + 1] - 1] = 0;
    *labp = lab; *ptnp = ptn;
    free(deg); free(W); free(ht); free(om); free(L8.w); free(L10.w);
    return 0;
}

int main(int argc, char **argv) {
    FILE *f = argc > 1 ? fopen(argv[1], "r") : stdin;
    static char line[16384];
    while (fgets(line, sizeof line, f)) {
        char *p = strstr(line, "| "); const char *code = p ? p + 2 : line;
        long idx = -1; sscanf(line, "%ld", &idx);
        v24 rows[12];
        const char *q = parse_rows_B(code, rows, 12);
        if (!q) { printf("%ld PARSEERR\n", idx); continue; }
        unsigned long long aut = 0; int a8 = 0, sc = 0, eb = 0; sscanf(q, "%llu %d %d %d", &aut, &a8, &sc, &eb);
        sparsegraph sg1, sg2, cg1, cg2; int *lab1, *ptn1, *lab2, *ptn2, nw1, nw2, r1, r2;
        if (build(rows, 0, &sg1, &lab1, &ptn1, &nw1, &r1) || build(rows, 1, &sg2, &lab2, &ptn2, &nw2, &r2)) { printf("%ld BUILDERR\n", idx); continue; }
        int n = sg1.nv;
        DEFAULTOPTIONS_SPARSEGRAPH(opt);
        statsblk st1, st2;
        opt.getcanon = TRUE; opt.defaultptn = FALSE;
        int *orb = malloc(sizeof(int) * (size_t)n);
        SG_INIT(cg1); SG_INIT(cg2);
        print_gens = getenv("GENS") != NULL; opt.userautomproc = ugen;
        sparsenauty(&sg1, lab1, ptn1, orb, &opt, &st1, &cg1);
        print_gens = 0; opt.userautomproc = NULL;
        int sameshape = (sg2.nv == n && sg2.nde == sg1.nde);
        int selfc = 0; uint64_t ckey = 0;
        if (sameshape) {
            int *orb2 = malloc(sizeof(int) * (size_t)n);
            sparsenauty(&sg2, lab2, ptn2, orb2, &opt, &st2, &cg2);
            sortlists_sg(&cg1); sortlists_sg(&cg2);
            selfc = aresame_sg(&cg1, &cg2) ? 1 : 0;
            uint64_t h1 = 0x9e3779b97f4a7c15ULL, h2 = 0x9e3779b97f4a7c15ULL;
            for (int v = 0; v < cg1.nv; v++) { h1 = smix(h1 ^ (uint64_t)cg1.d[v]); for (int q = 0; q < cg1.d[v]; q++) h1 = smix(h1 ^ (uint64_t)cg1.e[cg1.v[v] + q] ^ ((uint64_t)v << 32)); }
            for (int v = 0; v < cg2.nv; v++) { h2 = smix(h2 ^ (uint64_t)cg2.d[v]); for (int q = 0; q < cg2.d[v]; q++) h2 = smix(h2 ^ (uint64_t)cg2.e[cg2.v[v] + q] ^ ((uint64_t)v << 32)); }
            ckey = h1 < h2 ? h1 : h2;
            free(orb2);
        }
        double g = st1.grpsize1 * pow(10.0, (double)st1.grpsize2);
        printf("%ld field_aut=%llu field_sc=%d my_aut=%.0f my_sc=%d nwords=%d rank8=%d %s ckey=%016llx\n", idx, aut, sc, g, selfc, nw1, r1,
               ((unsigned long long)(g + 0.5) == aut && selfc == sc) ? "OK" : "MISMATCH", (unsigned long long)ckey);
        fflush(stdout);
        SG_FREE(sg1); SG_FREE(sg2); SG_FREE(cg1); if (sameshape) SG_FREE(cg2);
        free(lab1); free(ptn1); free(lab2); free(ptn2); free(orb);
    }
    return 0;
}
