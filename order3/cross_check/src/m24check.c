/* m24check.c -- verify, with own code, the M24 facts used by the point-placement normal form:
   (1) generators of PSL(2,23) and Conway's extra generator preserve the code (so they lie in M24 = Aut(G));
   (2) the group they generate is 5-transitive on ordered 5-tuples (BFS orbit of size 24*23*22*21*20);
   (3) the pointwise stabiliser H of 5 points of an octad O0 has order 48, induces exactly the 3 rotations on the
       other 3 points of O0, and its kernel K (order 16) is regular on the 16 points outside O0;
   (4) |Aut(G)| = 5100480 * 48 = 244823040 then follows from (2)+(3). */
#include "golay24.h"
#define INF 23
static int inv23(int x) { for (int y = 1; y < 23; y++) if ((x * y) % 23 == 1) return y; return -1; }
static int isqr(int x) { for (int y = 1; y < 23; y++) if ((y * y) % 23 == x) return 1; return 0; }
static int gens[4][24];
static uint8_t *seen;
static int enc(const int *t) { int e = 0; for (int i = 0; i < 5; i++) e = e * 24 + t[i]; return e; }
static int cntH = 0, rot[3][3], nker = 0;
static int stabs[64][24];
static int pm[24], used[24];
static void bt(int k, const int *order) {   /* assign images of order[k..23] */
    if (k == 24) {
        for (int i = 0; i < 759; i++) { uint32_t im = perm_apply(pm, OCT[i]); int ok = 0; for (int j = 0; j < 759; j++) if (OCT[j] == im) { ok = 1; break; } if (!ok) return; }
        if (cntH < 64) memcpy(stabs[cntH], pm, sizeof pm);
        cntH++; return;
    }
    int p = order[k];
    for (int c = 0; c < 24; c++) if (!used[c]) {
        pm[p] = c; used[c] = 1;
        /* prune: every octad whose points are all assigned must map to an octad */
        int ok = 1;
        for (int i = 0; i < 759 && ok; i++) {
            uint32_t o = OCT[i]; int all = 1;
            for (uint32_t t = o; t; t &= t - 1) { int q = __builtin_ctz(t); int assigned = 0; for (int j = 0; j <= k; j++) if (order[j] == q) { assigned = 1; break; } if (!assigned) { all = 0; break; } }
            if (all) { uint32_t im = perm_apply(pm, o); int f = 0; for (int j = 0; j < 759; j++) if (OCT[j] == im) { f = 1; break; } if (!f) ok = 0; }
        }
        if (ok) bt(k + 1, order);
        used[c] = 0;
    }
}
int main(void) {
    golay_build();
    /* alpha: x->x+1, beta: x->2x, gamma: x->-1/x, delta: x->x^3/9 (x in Q), 9x^3 (x in N); 0,inf fixed by beta,delta */
    for (int x = 0; x < 24; x++) {
        if (x == INF) { gens[0][x] = INF; gens[1][x] = INF; gens[2][x] = 0; gens[3][x] = INF; continue; }
        gens[0][x] = (x + 1) % 23;
        gens[1][x] = (2 * x) % 23;
        gens[2][x] = (x == 0) ? INF : (23 - inv23(x)) % 23;
        if (x == 0) gens[3][x] = 0;
        else { int x3 = (x * x % 23) * x % 23; gens[3][x] = isqr(x) ? (x3 * inv23(9)) % 23 : (9 * x3) % 23; }
    }
    const char *nm[4] = { "alpha x+1", "beta 2x", "gamma -1/x", "delta" };
    int ngen = 0, use[4];
    for (int g = 0; g < 4; g++) { int a = perm_is_aut(gens[g]); printf("%s preserves code: %d\n", nm[g], a); if (a) use[ngen++] = g; }
    /* BFS orbit of an ordered 5-tuple of points of an octad */
    uint32_t O0 = OCT[0]; int p[8], np = 0; for (uint32_t t = O0; t; t &= t - 1) p[np++] = __builtin_ctz(t);
    printf("O0 points:"); for (int i = 0; i < 8; i++) printf(" %d", p[i]); printf("\n");
    seen = calloc(24 * 24 * 24 * 24 * 24, 1);
    int *queue = malloc(sizeof(int) * 5200000); int qh = 0, qt = 0;
    int t0[5] = { p[0], p[1], p[2], p[3], p[4] };
    seen[enc(t0)] = 1; queue[qt++] = enc(t0);
    while (qh < qt) {
        int e = queue[qh++]; int t[5]; for (int i = 4; i >= 0; i--) { t[i] = e % 24; e /= 24; }
        for (int gi = 0; gi < ngen; gi++) { int u[5]; for (int i = 0; i < 5; i++) u[i] = gens[use[gi]][t[i]]; int f = enc(u); if (!seen[f]) { seen[f] = 1; queue[qt++] = f; } }
    }
    printf("orbit of ordered 5-tuple: %d (24*23*22*21*20 = %d)\n", qt, 24 * 23 * 22 * 21 * 20);
    /* pointwise stabiliser of p0..p4 by backtracking */
    int order[24], k = 0;
    for (int i = 0; i < 8; i++) order[k++] = p[i];
    for (int x = 0; x < 24; x++) if (!((O0 >> x) & 1)) order[k++] = x;
    memset(used, 0, sizeof used);
    for (int i = 0; i < 5; i++) { pm[p[i]] = p[i]; used[p[i]] = 1; }
    bt(5, order);
    printf("|pointwise stabiliser of 5 octad points| = %d\n", cntH);
    int nrot[3] = { 0, 0, 0 }; int kerreg = 1;
    int q1 = order[8];
    for (int s = 0; s < cntH && s < 64; s++) {
        int a = stabs[s][p[5]], b = stabs[s][p[6]], c = stabs[s][p[7]];
        int r = -1;
        if (a == p[5] && b == p[6] && c == p[7]) r = 0;
        else if (a == p[6] && b == p[7] && c == p[5]) r = 1;
        else if (a == p[7] && b == p[5] && c == p[6]) r = 2;
        if (r < 0) { printf("non-rotation on p6..p8!\n"); continue; }
        nrot[r]++;
        if (r == 0) { nker++; if (stabs[s][q1] == q1) { int id = 1; for (int x = 0; x < 24; x++) if (stabs[s][x] != x) id = 0; if (!id) kerreg = 0; } }
    }
    /* regularity: kernel elements map q1 to distinct points */
    int img[24] = { 0 }, distinct = 1;
    for (int s = 0; s < cntH && s < 64; s++) if (stabs[s][p[5]] == p[5] && stabs[s][p[6]] == p[6] && stabs[s][p[7]] == p[7]) { if (img[stabs[s][q1]]++) distinct = 0; }
    printf("rotations induced: id %d, r1 %d, r2 %d; kernel size %d; kernel regular on outside (q1=%d images distinct): %d %d\n", nrot[0], nrot[1], nrot[2], nker, q1, distinct, kerreg);
    printf("=> |M24| >= orbit*stab = %lld (expected 244823040)\n", (long long)qt * cntH);
    return 0;
}
