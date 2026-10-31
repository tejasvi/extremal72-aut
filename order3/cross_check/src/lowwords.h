/* lowwords.h -- all nonzero words of weight <= W (W <= 10) of a [24,12] self-dual F4 code, every scalar multiple
   included (independent code for the audit). Uses two complementary information sets I, J: a word of weight
   <= 10 has <= 5 nonzero coordinates on I or on J. */
#ifndef LOWWORDS_H
#define LOWWORDS_H
#include "f4a.h"
typedef struct { int n; int cap; v24 *w; } wlist;
static void wl_push(wlist *L, v24 x) {
    if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 4096; L->w = realloc(L->w, sizeof(v24) * (size_t)L->cap); }
    L->w[L->n++] = x;
}
static void lw_dfs(const v24 *g, int depth, int maxdepth, int start, v24 cur, uint32_t Imask, int jside, int wlo, int whi, wlist *L, int *bad) {
    for (int t = start; t < 12; t++) for (int s = 1; s <= 3; s++) {
        v24 nw = vadd(cur, vscal(g[t], s));
        int w = vwt(nw);
        int ni = __builtin_popcount(vsupp(nw) & Imask);
        int keep = jside ? (ni > maxdepth) : 1;
        if (keep) { if (w < 8) *bad = 1; if (w >= wlo && w <= whi) wl_push(L, nw); }
        if (depth + 1 < maxdepth) lw_dfs(g, depth + 1, maxdepth, t + 1, nw, Imask, jside, wlo, whi, L, bad);
    }
}
/* words with weight in [wlo,whi], whi <= 10; returns 0 ok, -1 rank deficiency, 1 if a word of weight < 8 found */
static int lowwords(const v24 *rows, int wlo, int whi, wlist *L) {
    v24 g[12]; memcpy(g, rows, sizeof g);
    int order[24]; for (int i = 0; i < 24; i++) order[i] = i;
    int piv[12];
    if (f4_rref(g, 12, order, 24, piv) < 12) return -1;
    uint32_t Imask = 0; for (int t = 0; t < 12; t++) Imask |= 1u << piv[t];
    v24 h[12]; memcpy(h, g, sizeof h);
    int jo[24], nj = 0; for (int i = 0; i < 24; i++) if (!((Imask >> i) & 1)) jo[nj++] = i;
    int pj[12];
    if (f4_rref(h, 12, jo, nj, pj) < 12) return -1;
    int maxdepth = whi / 2;          /* weight <= whi  =>  <= whi/2 nonzeros on I or on J */
    int bad = 0; v24 z = { 0, 0 };
    lw_dfs(g, 0, maxdepth, 0, z, Imask, 0, wlo, whi, L, &bad);
    lw_dfs(h, 0, maxdepth, 0, z, Imask, 1, wlo, whi, L, &bad);
    return bad;
}
#endif
