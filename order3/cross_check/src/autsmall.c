/* autsmall.c -- |Aut_Mon(C)| and Mon-equivalence of C and conj(C) for small F4 codes (length n <= 32, dim k <= 6)
   via nauty on the OWN encoding of autnd.c (coordinate, value vertices; ALL nonzero codewords as vertices; the
   scalar action by subdivided arcs w - t - h - w*omega).  Zero coordinates give S3 instead of rotations on their
   value vertices: the group order is divided by 2^z (z = number of zero coordinates).
   input: c3class E_B lines "k KEY AUT[x2] GEN" (n given on the command line); output per line:
   lineno field_aut field_sc my_aut my_sc OK|MISMATCH */
#include "f4a.h"
#include "nauty.h"
#include "nausparse.h"
#include <math.h>
static int NB;
static int build(const v24 *rows, int k, int conjflag, sparsegraph *sg, int **labp, int **ptnp, int *zc) {
    v24 r[8]; for (int t = 0; t < k; t++) r[t] = conjflag ? vconj(rows[t]) : rows[t];
    int nw = 1; for (int t = 0; t < k; t++) nw *= 4; nw -= 1;
    v24 *W = malloc(sizeof(v24) * (size_t)nw);
    for (int m = 1; m <= nw; m++) { v24 x = { 0, 0 }; int mm = m; for (int t = 0; t < k; t++) { int s = mm & 3; mm >>= 2; if (s) x = vadd(x, vscal(r[t], s)); } W[m - 1] = x; }
    uint32_t cov = 0; for (int j = 0; j < nw; j++) cov |= vsupp(W[j]);
    *zc = NB - __builtin_popcount(cov);
    /* omega image index: word m has digits s_t; omega*word has digits omega*s_t */
    int *om = malloc(sizeof(int) * (size_t)nw);
    for (int m = 1; m <= nw; m++) { int mm = m, m2 = 0, mul = 1; for (int t = 0; t < k; t++) { int s = mm & 3; mm >>= 2; m2 += f4mul(s, 2) * mul; mul *= 4; } om[m - 1] = m2 - 1; }
    for (int j = 0; j < nw; j++) { v24 x = vmulw(W[j]); if (x.a != W[om[j]].a || x.b != W[om[j]].b) { fprintf(stderr, "omega index error\n"); exit(2); } }
    int nc = NB, nval = 3 * NB, base = nc + nval;
    int nv = base + 3 * nw;
    int *deg = calloc((size_t)nv, sizeof(int));
    for (int i = 0; i < NB; i++) { deg[i] = 3; for (int s = 0; s < 3; s++) deg[nc + 3 * i + s] = 1; }
    for (int j = 0; j < nw; j++) {
        deg[base + j] += vwt(W[j]) + 2; deg[base + nw + j] = 2; deg[base + 2 * nw + j] = 2;
        for (uint32_t s = vsupp(W[j]); s; s &= s - 1) { int i = __builtin_ctz(s); deg[nc + 3 * i + vget(W[j], i) - 1]++; }
    }
    size_t ne = 0; for (int v = 0; v < nv; v++) ne += (size_t)deg[v];
    SG_INIT(*sg); SG_ALLOC(*sg, nv, ne, "sg"); sg->nv = nv; sg->nde = ne;
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg->v[v] = pos; sg->d[v] = 0; pos += (size_t)deg[v]; }
#define ADDE(x, y) do { sg->e[sg->v[x] + sg->d[x]++] = (y); sg->e[sg->v[y] + sg->d[y]++] = (x); } while (0)
    for (int i = 0; i < NB; i++) for (int s = 0; s < 3; s++) ADDE(i, nc + 3 * i + s);
    for (int j = 0; j < nw; j++) {
        int wv = base + j, tv = base + nw + j, hv = base + 2 * nw + j;
        for (uint32_t s = vsupp(W[j]); s; s &= s - 1) { int i = __builtin_ctz(s); ADDE(wv, nc + 3 * i + vget(W[j], i) - 1); }
        ADDE(wv, tv); ADDE(tv, hv); ADDE(hv, base + om[j]);
    }
    for (int v = 0; v < nv; v++) if (sg->d[v] != deg[v]) { fprintf(stderr, "deg mismatch\n"); exit(3); }
    int *lab = malloc(sizeof(int) * (size_t)nv), *ptn = malloc(sizeof(int) * (size_t)nv);
    int kk = 0, cst[6];
    for (int c = 0; c < 5; c++) { cst[c] = kk; for (int v = 0; v < nv; v++) { int cv = v < nc ? 0 : v < base ? 1 : v < base + nw ? 2 : v < base + 2 * nw ? 3 : 4; if (cv == c) lab[kk++] = v; } }
    cst[5] = kk;
    for (int i = 0; i < nv; i++) ptn[i] = 1;
    for (int c = 0; c < 5; c++) if (cst[c + 1] > cst[c]) ptn[cst[c + 1] - 1] = 0;
    *labp = lab; *ptnp = ptn; free(deg); free(W); free(om);
    return 0;
}
int main(int argc, char **argv) {
    NB = atoi(argv[1]);
    FILE *f = fopen(argv[2], "r"); static char line[8192]; long ln = -1;
    while (fgets(line, sizeof line, f)) {
        ln++;
        int k; char key[512], autf[64], gen[512];
        if (sscanf(line, "%d %511s %63s %511s", &k, key, autf, gen) != 4) { printf("%ld PARSEERR\n", ln); continue; }
        v24 rows[8]; if (!parse_rows_B(gen, rows, k)) { printf("%ld PARSEERR2\n", ln); continue; }
        int fsc = strstr(autf, "x2") ? 0 : 1; double faut = atof(autf);
        sparsegraph s1, s2, c1, c2; int *l1, *p1, *l2, *p2, z1, z2;
        build(rows, k, 0, &s1, &l1, &p1, &z1); build(rows, k, 1, &s2, &l2, &p2, &z2);
        DEFAULTOPTIONS_SPARSEGRAPH(opt); statsblk st; opt.getcanon = TRUE; opt.defaultptn = FALSE;
        int *orb = malloc(sizeof(int) * (size_t)s1.nv);
        SG_INIT(c1); SG_INIT(c2);
        sparsenauty(&s1, l1, p1, orb, &opt, &st, &c1);
        double g = st.grpsize1 * pow(10.0, (double)st.grpsize2) / pow(2.0, (double)z1);
        sparsenauty(&s2, l2, p2, orb, &opt, &st, &c2);
        sortlists_sg(&c1); sortlists_sg(&c2);
        int sc = aresame_sg(&c1, &c2) ? 1 : 0;
        uint64_t h1 = 0x9e3779b97f4a7c15ULL, h2 = 0x9e3779b97f4a7c15ULL;
        for (int v = 0; v < c1.nv; v++) { h1 = smix(h1 ^ (uint64_t)c1.d[v]); for (int q = 0; q < c1.d[v]; q++) h1 = smix(h1 ^ (uint64_t)c1.e[c1.v[v] + q] ^ ((uint64_t)v << 32)); }
        for (int v = 0; v < c2.nv; v++) { h2 = smix(h2 ^ (uint64_t)c2.d[v]); for (int q = 0; q < c2.d[v]; q++) h2 = smix(h2 ^ (uint64_t)c2.e[c2.v[v] + q] ^ ((uint64_t)v << 32)); }
        uint64_t ckey = h1 < h2 ? h1 : h2;
        int ok = (fabs(g - faut) < 0.5) && sc == fsc;
        printf("%ld field_aut=%.0f field_sc=%d my_aut=%.0f my_sc=%d zero=%d %s ckey=%016llx\n", ln, faut, fsc, g, sc, z1, ok ? "OK" : "MISMATCH", (unsigned long long)ckey);
        SG_FREE(s1); SG_FREE(s2); SG_FREE(c1); SG_FREE(c2); free(l1); free(p1); free(l2); free(p2); free(orb);
    }
    return 0;
}
