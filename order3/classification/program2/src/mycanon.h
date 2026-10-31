/* c3explore canonical form of an F4-linear code under monomial maps (and Mon x conjugation), written
   independently of c3class's cform.h.  Graph: coordinate-value vertices V(i,l) = 3i + (l-1) for l in F4^* (codes
   1, w=2, wbar=3), directed edges V(i,l) -> V(i, w*l) (a directed 3-cycle per coordinate, so graph maps rotate
   each triple = scale the coordinate); one vertex per nonzero codeword (all scalar multiples included), joined in
   both directions to V(i, c_i) for each coordinate i in its support.  Word set = ALL nonzero codewords (k <= 6),
   so automorphisms of the graph are exactly the monomial automorphisms of the code (scalars included).
   Canonical code: coordinates ordered by the first canonical position of their three vertices, coordinate i scaled
   so that its first vertex has value 1, then reduced row echelon form (pivot = lowest coordinate, leading 1). */
#ifndef MYCANON_H
#define MYCANON_H
#include "../f4code.h"
#include "nauty/nauty.h"
#include "nauty/nausparse.h"
#include <math.h>
static int mc_log_inv[4] = { 0, 1, 3, 2 };         /* inverse in F4^* by element code */
/* canonical form of code given by k generators (k <= 6) of length n (<= 32); returns canonical RREF in out[0..k-1],
   |Aut_Mon| in *aut.  Returns rank. */
static int mc_canon(const vec *gen, int k, int n, vec *out, double *aut) {
    vec rows[16]; memcpy(rows, gen, sizeof(vec) * k); int piv[16];
    int rk = vrref(rows, k, n, piv);
    long nw = 1; for (int i = 0; i < rk; i++) nw *= 4; nw -= 1;
    vec *W = malloc(sizeof(vec) * (nw + 1)); vec *all = malloc(sizeof(vec) * (nw + 1));
    combos(rows, rk, all);                       /* all[0] = 0 */
    long m = 0; for (long i = 1; i <= nw; i++) W[m++] = all[i];
    free(all);
    int nv = 3 * n + (int)m;
    size_t ne = 3 * n; for (long j = 0; j < m; j++) ne += 2 * (size_t)vwt(W[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "mc_canon");
    sg.nv = nv; sg.nde = ne;
    int *deg = calloc(nv, sizeof(int));
    for (int v = 0; v < 3 * n; v++) deg[v] = 1;
    for (long j = 0; j < m; j++) { u32 s = vsupp(W[j]); deg[3 * n + j] = __builtin_popcount(s); for (; s; s &= s - 1) { int i = __builtin_ctz(s); deg[3 * i + vget(W[j], i) - 1]++; } }
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int l = 1; l <= 3; l++) { int v = 3 * i + l - 1; int nl = f4mul[l][2]; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + nl - 1; }
    for (long j = 0; j < m; j++) { int y = 3 * n + (int)j;
        for (u32 s = vsupp(W[j]); s; s &= s - 1) { int i = __builtin_ctz(s); int x = 3 * i + vget(W[j], i) - 1;
            sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y; } }
    free(deg);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    for (int v = 0; v < nv; v++) { lab[v] = v; ptn[v] = 1; }
    ptn[3 * n - 1] = 0; ptn[nv - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt); opt.getcanon = TRUE; opt.defaultptn = FALSE;
    statsblk st; SG_DECL(cg);
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, &cg);
    *aut = st.grpsize1 * pow(10.0, st.grpsize2);
    int *where = malloc(sizeof(int) * nv); for (int p = 0; p < nv; p++) where[lab[p]] = p;
    int firstpos[32], firstl[32], ord[32];
    for (int i = 0; i < n; i++) { firstpos[i] = 1 << 30; for (int l = 1; l <= 3; l++) { int p = where[3 * i + l - 1]; if (p < firstpos[i]) { firstpos[i] = p; firstl[i] = l; } } ord[i] = i; }
    for (int a = 1; a < n; a++) { int t = ord[a], b = a; while (b > 0 && firstpos[ord[b - 1]] > firstpos[t]) { ord[b] = ord[b - 1]; b--; } ord[b] = t; }
    int newc[32]; for (int p = 0; p < n; p++) newc[ord[p]] = p;
    for (int r = 0; r < rk; r++) { vec x = {0, 0};
        for (int i = 0; i < n; i++) { int c = vget(rows[r], i); if (c) vset(&x, newc[i], f4mul[c][mc_log_inv[firstl[i]]]); }
        out[r] = x; }
    int p2[16]; vrref(out, rk, n, p2);
    free(where); free(lab); free(ptn); free(orb); free(W);
    SG_FREE(sg); SG_FREE(cg);
    return rk;
}
static int mc_cmp(const vec *a, const vec *b, int k) { for (int r = 0; r < k; r++) { if (a[r].lo != b[r].lo) return a[r].lo < b[r].lo ? -1 : 1; if (a[r].hi != b[r].hi) return a[r].hi < b[r].hi ? -1 : 1; } return 0; }
/* class key under Mon x conj: min(canon(C), canon(conj C)); selfconj = equal */
static int mc_class(const vec *gen, int k, int n, vec *key, double *aut, int *selfconj) {
    vec c1[16], c2[16], g2[16]; double a1, a2;
    int rk = mc_canon(gen, k, n, c1, &a1);
    for (int r = 0; r < k; r++) { g2[r].lo = gen[r].lo ^ gen[r].hi; g2[r].hi = gen[r].hi; }   /* conjugation */
    mc_canon(g2, k, n, c2, &a2);
    int c = mc_cmp(c1, c2, rk);
    memcpy(key, c <= 0 ? c1 : c2, sizeof(vec) * rk); *aut = a1; *selfconj = (c == 0);
    return rk;
}
#endif
