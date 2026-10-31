/* c3explore canonical form for longer codes (k up to 16): same graph as mycanon.h (coordinate-value triples with
   directed 3-cycles, one vertex per word) but on a given word set W instead of all codewords.  W must be closed
   under scalars, invariant under all monomial automorphisms of the code (e.g. ALL words of weight <= w) and span
   the code; then graph automorphisms = monomial automorphisms and the canonical code is a class invariant. */
#ifndef MYCANON2_H
#define MYCANON2_H
#include "mycanon.h"
static int mc_canon_wl(const vec *gen, int k, int n, const vec *W, long m, vec *out, double *aut) {
    vec rows[32]; memcpy(rows, gen, sizeof(vec) * k); int piv[32];
    int rk = vrref(rows, k, n, piv);
    int nv = 3 * n + (int)m;
    size_t ne = 3 * n; for (long j = 0; j < m; j++) ne += 2 * (size_t)vwt(W[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "mc_canon_wl");
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
    int p2[32]; vrref(out, rk, n, p2);
    free(where); free(lab); free(ptn); free(orb);
    SG_FREE(sg); SG_FREE(cg);
    return rk;
}
static inline vec mc_conjv(vec a) { vec r = { a.lo ^ a.hi, a.hi }; return r; }
/* class key under Mon x conj from a word set W of the code (conjugated internally for conj C) */
static int mc_class_wl(const vec *gen, int k, int n, const vec *W, long m, vec *key, double *aut, int *selfconj) {
    vec c1[32], c2[32], g2[32]; double a1, a2;
    int rk = mc_canon_wl(gen, k, n, W, m, c1, &a1);
    vec *W2 = malloc(sizeof(vec) * (m + 1)); for (long j = 0; j < m; j++) W2[j] = mc_conjv(W[j]);
    for (int r = 0; r < k; r++) g2[r] = mc_conjv(gen[r]);
    mc_canon_wl(g2, k, n, W2, m, c2, &a2); free(W2);
    int c = mc_cmp(c1, c2, rk);
    memcpy(key, c <= 0 ? c1 : c2, sizeof(vec) * rk); *aut = a1; *selfconj = (c == 0);
    return rk;
}
#endif
