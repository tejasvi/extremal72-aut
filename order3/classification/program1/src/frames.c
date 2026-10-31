/* R2 classification of Hermitian self-dual [n, n/2, d] codes over F4 (d = minimum weight, even).
   For E with a weight-d word e1 (support S1, scaled to 1^d), E_B = E^{S1}|_B is a self-orthogonal
   [n-d, n/2-d+1, >= d] code on B = complement of S1, E|_S1 = 1^perp, and E is the graph of an isometry
   phi: 1^perp/<1> -> V2 = E_B^perp/E_B (both of dimension d-2).  With z_d = 0 and y_i = phi(e_i + e_d):
   <y_i,y_j> = 1 (i != j), <y_i,y_i> = 0, sum_{i<d} y_i = 0; the frame {0, y_1..y_{d-1}} is an unordered d-set
   up to translation and scalars.  d(E) >= d <=> for every class [u] != 0 of 1^perp/<1>,
   minwt(phi(u) + E_B) >= M(u) = max_c #{i : u_i = c}.
   Enumeration: y_1 < ... < y_{d-2} (V2 indices) with all conditions on classes supported on {1..k, d},
   y_{d-1} = sum, y_{d-1} > y_{d-2}; frame kept iff its representation is minimal over the d origins and 3
   scalars.  Acceptance (one representative per code): e1's support must be in the canonical Aut(E)-orbit of
   weight-d supports (maximal intersection-profile invariant; nauty orbits/canonical labelling for ties).
   Usage: frames n d ebfile outfile [slice nslices]    ebfile lines: "kb key aut gen" (gen used).
   Output lines: classkey(hex rows) autMon A_d selfconj gen(hex rows) ebindex                               */
#include "cform.h"
#include <time.h>

static int n, d, nb, kb, m, nV;
static f4v Eb[8], Wb[8];
static f4v *rep; static uint8_t *mu, *nrm; static uint16_t *mulw, *mulw2;
static int *mwoff, *mwcnt; static uint32_t *mwsup; static int mwcap;      /* min-weight supports per coset */
static uint32_t ebd[1024]; static int nebd;                                /* E_B weight-d supports (projective) */
static int debugw = 0; static long nwdiff = 0;
static uint8_t *Mtab[16];
static long nleaf, ncanonfr, naccept, ntie, nnauty, nout;
static double tAcc;
static FILE *fout; static long ebindex; static int countonly = 0;

static inline int ip(int u, int v) { return f4herm(rep[u], rep[v]); }
static inline int smul(int lam, int v) { return lam == 1 ? v : lam == 2 ? mulw[v] : mulw2[v]; }

static void setup_V2(void) {
    f4v C[8]; memcpy(C, Eb, sizeof(f4v) * kb);
    int pc[8]; f4rref(C, kb, nb, pc, NULL);
    f4v D[32]; int dd = f4hermdual(C, kb, nb, D);
    f4v R[32]; int nr = 0;
    for (int i = 0; i < dd; i++) { f4v x = D[i]; for (int j = 0; j < kb; j++) { int e = f4get(x, pc[j]); if (e) x = f4add(x, f4smul(e, C[j])); } R[nr++] = x; }
    int pw[32]; int mm = f4rref(R, nr, nb, pw, NULL);
    if (mm != m) { fprintf(stderr, "V2 dim %d != %d\n", mm, m); exit(1); }
    memcpy(Wb, R, sizeof(f4v) * m);
    nV = 1 << (2 * m);
    rep = realloc(rep, sizeof(f4v) * nV); mu = realloc(mu, nV); nrm = realloc(nrm, nV);
    mulw = realloc(mulw, 2 * nV); mulw2 = realloc(mulw2, 2 * nV);
    int nwe = 1 << (2 * kb); f4v *ew = malloc(sizeof(f4v) * nwe);
    for (int t = 0; t < nwe; t++) { f4v x = { 0, 0 }; for (int j = 0; j < kb; j++) x = f4add(x, f4smul((t >> (2 * j)) & 3, Eb[j])); ew[t] = x; }
    for (int v = 0; v < nV; v++) {
        f4v x = { 0, 0 }; int v2 = 0, v3 = 0;
        for (int j = 0; j < m; j++) { int c = (v >> (2 * j)) & 3; x = f4add(x, f4smul(c, Wb[j])); v2 |= F4MUL[2][c] << (2 * j); v3 |= F4MUL[3][c] << (2 * j); }
        rep[v] = x; mulw[v] = v2; mulw2[v] = v3; nrm[v] = f4wt(x) & 1;
        int mw = 99; for (int t = 0; t < nwe; t++) { int w = f4wt(f4add(x, ew[t])); if (w < mw) mw = w; }
        mu[v] = mw;
    }
    mwoff = realloc(mwoff, sizeof(int) * nV); mwcnt = realloc(mwcnt, sizeof(int) * nV);
    int tot = 0;
    for (int v = 0; v < nV; v++) {
        mwoff[v] = tot; mwcnt[v] = 0;
        if (v == 0) continue;
        for (int t = 0; t < nwe; t++) {
            f4v z = f4add(rep[v], ew[t]);
            if (f4wt(z) == mu[v]) {
                if (tot == mwcap) { mwcap = mwcap ? 2 * mwcap : 65536; mwsup = realloc(mwsup, 4 * mwcap); }
                mwsup[tot++] = f4supp(z); mwcnt[v]++;
            }
        }
    }
    nebd = 0;
    for (int t = 1; t < nwe; t++) if (f4wt(ew[t]) == d) {
        uint32_t sp = f4supp(ew[t]); int dup = 0;
        for (int j = 0; j < nebd; j++) if (ebd[j] == sp) { dup = 1; break; }
        if (!dup) ebd[nebd++] = sp;
    }
    free(ew);
}
static uint64_t *ipone;           /* ipone[v*NW + w]: bit u set iff <rep u, rep v> = 1 (rows for usable v) */
static uint64_t valid1[64];
static int NW;
static void setup_bitsets(void) {
    NW = (nV + 63) / 64;
    ipone = realloc(ipone, sizeof(uint64_t) * nV * NW);
    memset(valid1, 0, sizeof valid1);
    for (int v = 1; v < nV; v++) if (!nrm[v] && mu[v] >= d - 2) valid1[v >> 6] |= 1ULL << (v & 63);
    for (int v = 1; v < nV; v++) {
        uint64_t *row = ipone + (size_t)v * NW;
        memset(row, 0, 8 * NW);
        if (!((valid1[v >> 6] >> (v & 63)) & 1)) continue;
        for (int u = 1; u < nV; u++) if (((valid1[u >> 6] >> (u & 63)) & 1) && ip(u, v) == 1
                                         && mu[u ^ v] >= d - 2 && mu[u ^ mulw[v]] >= d - 3 && mu[u ^ mulw2[v]] >= d - 3)
            row[u >> 6] |= 1ULL << (u & 63);
    }
}
static void setup_Mtab(void) {
    for (int k = 1; k <= d - 2; k++) {
        int sz = 1 << (2 * k);
        Mtab[k] = realloc(Mtab[k], sz);
        for (int c = 0; c < sz; c++) {
            int cnt[4] = { 0 }, s = 0;
            for (int i = 0; i < k; i++) { int u = (c >> (2 * i)) & 3; cnt[u]++; s ^= u; }
            cnt[0] += d - 1 - k; cnt[s]++;
            int mx = 0; for (int t = 0; t < 4; t++) if (cnt[t] > mx) mx = cnt[t];
            Mtab[k][c] = mx;
        }
    }
}
/* ---------------- acceptance ---------------- */
typedef struct { uint32_t *s; int n, cap; } slist_t;
static void scb(f4v w, int nrows, void *c) {
    slist_t *L = (slist_t *)c;
    if (f4wt(w) > d) return;
    if (f4wt(w) < d) { fprintf(stderr, "weight %d word found: frame conditions wrong\n", f4wt(w)); exit(1); }
    if (L->n == L->cap) { L->cap = L->cap ? 2 * L->cap : 1024; L->s = realloc(L->s, 4 * L->cap); }
    L->s[L->n++] = f4supp(w);
}
static int cmpu(const void *a, const void *b) { uint32_t x = *(uint32_t *)a, y = *(uint32_t *)b; return x < y ? -1 : x > y; }
static uint64_t acc_key(const uint32_t *S, int ns, int i, int *hist) {
    int h[33] = { 0 };
    for (int j = 0; j < ns; j++) if (j != i) h[__builtin_popcount(S[i] & S[j])]++;
    uint64_t key = 0;
    for (int t = 0; t < d; t++) key = key * 4099 + h[t];
    if (hist) memcpy(hist, h, sizeof h);
    return key;
}
/* nauty canonical labelling of the graph on a spanning word set W (Y vertices coloured by weight d / heavier):
   returns canonical RREF matrix T of gen, coordinate ranks newpos[], and canonical positions / orbit ids of the
   Y vertices. */
static void canon_labelled(const f4v *W, int nw, const f4v *gen, int k, int *newpos, int *ypos, int *yorb, f4v *T) {
    int nv = 3 * n + nw;
    size_t ne = 3 * n; for (int j = 0; j < nw; j++) ne += 2 * (size_t)f4wt(W[j]);
    SG_DECL(sg); SG_ALLOC(sg, nv, ne, "cl"); sg.nv = nv; sg.nde = ne;
    int *deg = calloc(nv, sizeof(int));
    for (int i = 0; i < 3 * n; i++) deg[i] = 1;
    for (int j = 0; j < nw; j++) { uint32_t mm = f4supp(W[j]); deg[3 * n + j] = __builtin_popcount(mm); for (; mm; mm &= mm - 1) { int i = __builtin_ctz(mm); deg[3 * i + F4LOG[f4get(W[j], i)]]++; } }
    size_t pos = 0; for (int v = 0; v < nv; v++) { sg.v[v] = pos; sg.d[v] = 0; pos += deg[v]; }
    for (int i = 0; i < n; i++) for (int a = 0; a < 3; a++) { int v = 3 * i + a; sg.e[sg.v[v] + sg.d[v]++] = 3 * i + (a + 1) % 3; }
    for (int j = 0; j < nw; j++) { int y = 3 * n + j; for (uint32_t mm = f4supp(W[j]); mm; mm &= mm - 1) { int i = __builtin_ctz(mm), x = 3 * i + F4LOG[f4get(W[j], i)]; sg.e[sg.v[y] + sg.d[y]++] = x; sg.e[sg.v[x] + sg.d[x]++] = y; } }
    free(deg);
    int *lab = malloc(sizeof(int) * nv), *ptn = malloc(sizeof(int) * nv), *orb = malloc(sizeof(int) * nv);
    for (int v = 0; v < 3 * n; v++) { lab[v] = v; ptn[v] = 1; }
    int q = 3 * n, nyd = 0;
    for (int j = 0; j < nw; j++) if (f4wt(W[j]) == d) { lab[q] = 3 * n + j; ptn[q] = 1; q++; nyd++; }
    for (int j = 0; j < nw; j++) if (f4wt(W[j]) != d) { lab[q] = 3 * n + j; ptn[q] = 1; q++; }
    ptn[3 * n - 1] = 0; ptn[3 * n + nyd - 1] = 0; ptn[nv - 1] = 0;
    DEFAULTOPTIONS_SPARSEDIGRAPH(opt);
    opt.getcanon = TRUE; opt.defaultptn = FALSE;
    statsblk st; SG_DECL(cg);
    sparsenauty(&sg, lab, ptn, orb, &opt, &st, &cg);
    int *posv = malloc(sizeof(int) * nv); for (int p = 0; p < nv; p++) posv[lab[p]] = p;
    int first[32], ai[32], order[32];
    for (int i = 0; i < n; i++) {
        int best = 1 << 30, ba = 0;
        for (int a = 0; a < 3; a++) if (posv[3 * i + a] < best) { best = posv[3 * i + a]; ba = a; }
        first[i] = best; ai[i] = ba; order[i] = i;
    }
    for (int i = 1; i < n; i++) { int t = order[i], j = i; while (j > 0 && first[order[j - 1]] > first[t]) { order[j] = order[j - 1]; j--; } order[j] = t; }
    for (int p = 0; p < n; p++) newpos[order[p]] = p;
    for (int r = 0; r < k; r++) {
        f4v x = { 0, 0 };
        for (int i = 0; i < n; i++) { int e = f4get(gen[r], i); if (e) f4set(&x, newpos[i], F4MUL[e][F4EXP[(3 - ai[i]) % 3]]); }
        T[r] = x;
    }
    int piv[32]; f4rref(T, k, n, piv, NULL);
    for (int j = 0; j < nw; j++) { ypos[j] = posv[3 * n + j]; yorb[j] = orb[3 * n + j]; }
    free(posv); free(lab); free(ptn); free(orb); SG_FREE(sg); SG_FREE(cg);
}
static int ufs[4096];
static int ufs_find(int x) { while (ufs[x] != x) { ufs[x] = ufs[ufs[x]]; x = ufs[x]; } return x; }
static void ufs_union(int a, int b) { a = ufs_find(a); b = ufs_find(b); if (a != b) ufs[a] = b; }
/* canonical orbit choice among tied supports, invariant under monomial maps and conjugation */
static int nauty_choice(const f4v *gen, uint32_t S1, const uint32_t *tied, int nt) {
    nnauty++;
    int k = n / 2;
    wlist_t L = { 0, 0, 0 };
    int wmax = d;
    for (;;) {
        L.n = 0; select_words(gen, k, n, d, wmax, &L);
        f4v Rr[16]; int r = 0;
        for (int j = 0; j < L.n && r < k; j++) { Rr[r] = L.w[j]; if (f4rank(Rr, r + 1, n) == r + 1) r++; }
        if (r == k) break;
        wmax += 2;
    }
    int nw = L.n;
    f4v *Wc = malloc(sizeof(f4v) * nw); for (int j = 0; j < nw; j++) Wc[j] = f4conj(L.w[j]);
    f4v genc[16]; for (int r = 0; r < k; r++) genc[r] = f4conj(gen[r]);
    int npE[32], npC[32]; int *yposE = malloc(sizeof(int) * nw), *yorbE = malloc(sizeof(int) * nw), *yposC = malloc(sizeof(int) * nw), *yorbC = malloc(sizeof(int) * nw);
    f4v TE[16], TC[16];
    canon_labelled(L.w, nw, gen, k, npE, yposE, yorbE, TE);
    canon_labelled(Wc, nw, genc, k, npC, yposC, yorbC, TC);
    int c = mat_cmp(TE, TC, k);
    int *ypos = c <= 0 ? yposE : yposC, *yorb = c <= 0 ? yorbE : yorbC;
    /* tied support index of each weight-d word */
    for (int t = 0; t < nt; t++) ufs[t] = t;
    int *tix = malloc(sizeof(int) * nw);
    int bestpos = 1 << 30, bestt = -1, t1 = -1;
    for (int t = 0; t < nt; t++) if (tied[t] == S1) t1 = t;
    for (int j = 0; j < nw; j++) {
        tix[j] = -1;
        if (f4wt(L.w[j]) != d) continue;
        uint32_t sp = f4supp(L.w[j]);
        for (int t = 0; t < nt; t++) if (tied[t] == sp) { tix[j] = t; break; }
        if (tix[j] < 0) continue;
        if (ypos[j] < bestpos) { bestpos = ypos[j]; bestt = tix[j]; }
    }
    /* Aut_Mon orbits: words in the same orbit -> same class */
    for (int j = 0; j < nw; j++) if (tix[j] >= 0)
        for (int j2 = 0; j2 < nw; j2++) if (tix[j2] >= 0 && yorb[j2] == yorb[j]) { ufs_union(tix[j], tix[j2]); break; }
    if (c == 0) {
        /* self-conjugate: sigma(i) = npC^{-1}[npE[i]] permutes supports (semilinear automorphism) */
        int inv[32]; for (int i = 0; i < n; i++) inv[npC[i]] = i;
        for (int t = 0; t < nt; t++) {
            uint32_t img = 0; for (uint32_t mm = tied[t]; mm; mm &= mm - 1) img |= 1u << inv[npE[__builtin_ctz(mm)]];
            for (int t2 = 0; t2 < nt; t2++) if (tied[t2] == img) { ufs_union(t, t2); break; }
        }
    }
    int ok = (t1 >= 0 && bestt >= 0 && ufs_find(t1) == ufs_find(bestt));
    free(tix); free(Wc); free(yposE); free(yorbE); free(yposC); free(yorbC); free(L.w);
    return ok;
}
static uint16_t *phi[16];
static int frame_supports(uint32_t *out) {
    int ns = 0;
    out[ns++] = (1u << d) - 1;
    for (int j = 0; j < nebd; j++) out[ns++] = ebd[j] << d;
    int K = d - 2, sz = 1 << (2 * K);
    const uint16_t *P = phi[K];
    for (int c = 1; c < sz; c++) {
        int lo = __builtin_ctz(c) & ~1; if (((c >> lo) & 3) != 1) continue;     /* first nonzero coefficient 1 */
        int v = P[c], M = Mtab[K][c];
        if (mu[v] != M) continue;
        int u[16], cnt[4] = { 0 }, s = 0;
        for (int i = 0; i < K; i++) { u[i] = (c >> (2 * i)) & 3; cnt[u[i]]++; s ^= u[i]; }
        u[K] = 0; cnt[0]++; u[K + 1] = s; cnt[s]++;
        for (int lam = 0; lam < 4; lam++) if (cnt[lam] == M) {
            uint32_t s1 = 0; for (int i = 0; i < d; i++) if (u[i] != lam) s1 |= 1u << i;
            for (int t = 0; t < mwcnt[v]; t++) out[ns++] = s1 | (mwsup[mwoff[v] + t] << d);
        }
    }
    return ns;
}
static void accept_and_output(const f4v *gen) {
    double t0 = (double)clock();
    static slist_t L = { 0, 0, 0 };
    if (L.cap < 8192) { L.cap = 8192; L.s = realloc(L.s, 4 * L.cap); }
    int ns = frame_supports(L.s);
    if (debugw) {
        static slist_t L2 = { 0, 0, 0 }; L2.n = 0;
        sd_lowwords(gen, n, d, scb, &L2);
        qsort(L2.s, L2.n, 4, cmpu);
        int n2 = 0; for (int i = 0; i < L2.n; i++) if (!n2 || L2.s[n2 - 1] != L2.s[i]) L2.s[n2++] = L2.s[i];
        uint32_t *tmp = malloc(4 * ns); memcpy(tmp, L.s, 4 * ns); qsort(tmp, ns, 4, cmpu);
        if (n2 != ns || memcmp(tmp, L2.s, 4 * ns)) nwdiff++;
        free(tmp);
    }
    uint32_t S1 = (1u << d) - 1;
    int i1 = -1; for (int i = 0; i < ns; i++) if (L.s[i] == S1) i1 = i;
    if (i1 < 0) { fprintf(stderr, "e1 support missing\n"); exit(1); }
    uint64_t k1 = acc_key(L.s, ns, i1, NULL);
    int ties = 0;
    for (int i = 0; i < ns; i++) {
        if (i == i1) continue;
        uint64_t ki = acc_key(L.s, ns, i, NULL);
        if (ki > k1) { tAcc += (double)clock() - t0; return; }        /* not canonical */
        if (ki == k1) ties++;
    }
    if (ties) {
        ntie++;
        uint32_t *tied = malloc(4 * (ties + 1)); int nt = 0;
        for (int i = 0; i < ns; i++) if (acc_key(L.s, ns, i, NULL) == k1) tied[nt++] = L.s[i];
        int ok = nauty_choice(gen, S1, tied, nt);
        free(tied);
        if (!ok) { tAcc += (double)clock() - t0; return; }
    }
    naccept++;
    f4v key[16]; double az; int sc;
    if (canon_class(gen, n / 2, n, d, key, &az, &sc)) { fprintf(stderr, "canon failed\n"); exit(1); }
    for (int r = 0; r < n / 2; r++) fprintf(fout, "%08x%08x", key[r].a, key[r].b);
    fprintf(fout, " %.0f %d %d", az, ns * 3, sc);
    if (getenv("WRITEGEN")) { fprintf(fout, " "); for (int r = 0; r < n / 2; r++) fprintf(fout, "%08x%08x", gen[r].a, gen[r].b); }
    fprintf(fout, " %ld\n", ebindex);
    nout++;
    tAcc += (double)clock() - t0;
}
/* ---------------- frame search ---------------- */
static int y[16];
static void leaf(void) {
    int last = 0; for (int i = 1; i <= d - 2; i++) last ^= y[i];
    if (last <= y[d - 2]) return;
    { int y1 = y[1]; if (mulw[last] < y1 || mulw2[last] < y1) return;
      for (int j = 1; j <= d - 2; j++) { int t = last ^ y[j]; if (t < y1 || mulw[t] < y1 || mulw2[t] < y1) return; } }
    y[d - 1] = last;
    nleaf++;
    /* canonical representation over origins and scalars */
    int cur[16]; for (int i = 1; i < d; i++) cur[i - 1] = y[i];
    for (int j = 0; j < d; j++) for (int lam = 1; lam <= 3; lam++) {
        if (j == d - 1 && lam == 1) continue;
        int alt[16], na = 0;
        int zj = (j == d - 1) ? 0 : y[j + 1];
        for (int i = 0; i < d; i++) {
            if (i == j) continue;
            int zi = (i == d - 1) ? 0 : y[i + 1];
            alt[na++] = smul(lam, zi ^ zj);
        }
        for (int a = 1; a < na; a++) { int t = alt[a], b = a; while (b > 0 && alt[b - 1] > t) { alt[b] = alt[b - 1]; b--; } alt[b] = t; }
        for (int a = 0; a < na; a++) { if (alt[a] < cur[a]) return; if (alt[a] > cur[a]) break; }
    }
    ncanonfr++;
    if (countonly) return;
    /* build E: coordinates 0..d-1 = S1 (origin point = d-1), d..n-1 = B */
    f4v gen[16]; int r = 0;
    f4v one = { 0, 0 }; for (int i = 0; i < d; i++) f4set(&one, i, 1);
    gen[r++] = one;
    for (int i = 1; i <= d - 2; i++) {
        f4v x = { 0, 0 }; f4set(&x, i - 1, 1); f4set(&x, d - 1, 1);
        x.a |= rep[y[i]].a << d; x.b |= rep[y[i]].b << d;
        gen[r++] = x;
    }
    for (int j = 0; j < kb; j++) { f4v x = { Eb[j].a << d, Eb[j].b << d }; gen[r++] = x; }
    if (f4rank(gen, r, n) != n / 2) { fprintf(stderr, "rank defect\n"); exit(1); }
    accept_and_output(gen);
}
static uint64_t candbs[16][64];
static void dfs(int k) {
    if (k > d - 2) { leaf(); return; }
    int sz = 1 << (2 * (k - 1));
    uint64_t *C = candbs[k];
    if (k == 1) memcpy(C, valid1, 8 * NW);
    else { const uint64_t *P = candbs[k - 1], *row = ipone + (size_t)y[k - 1] * NW; for (int w = 0; w < NW; w++) C[w] = P[w] & row[w]; }
    int start = y[k - 1] + 1;
    for (int w = start >> 6; w < NW; w++) {
        uint64_t bits = C[w];
        if (w == (start >> 6)) bits &= ~0ULL << (start & 63);
        while (bits) {
            int v = (w << 6) | __builtin_ctzll(bits); bits &= bits - 1;
            int ok = 1;
            int v2 = mulw[v], v3 = mulw2[v];
            /* translation/scalar canonicity (necessary): every element of every representation >= y_1 */
            if (k == 1) { if (v2 < v || v3 < v) continue; }
            else {
                int y1 = y[1];
                if (v2 < y1 || v3 < y1) continue;
                for (int j = 1; j < k && ok; j++) { int t = v ^ y[j]; if (t < y1 || mulw[t] < y1 || mulw2[t] < y1) ok = 0; }
                if (!ok) continue;
            }
            uint16_t *P = phi[k - 1], *Q = phi[k];
            const uint8_t *Mt = Mtab[k];
            for (int c = 0; c < sz && ok; c++) {
                int a = P[c] ^ v, b = P[c] ^ v2, e = P[c] ^ v3;
                if (mu[a] < Mt[c + sz] || mu[b] < Mt[c + 2 * sz] || mu[e] < Mt[c + 3 * sz]) ok = 0;
                Q[c + sz] = a; Q[c + 2 * sz] = b; Q[c + 3 * sz] = e;
            }
            if (!ok) continue;
            for (int c = 0; c < sz; c++) Q[c] = P[c];
            y[k] = v;
            dfs(k + 1);
        }
    }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); d = atoi(argv[2]);
    nb = n - d; kb = n / 2 - d + 1; m = d - 2;
    const char *ebfile = argv[3]; fout = fopen(argv[4], "w");
    int slice = argc > 5 ? atoi(argv[5]) : 0, nsl = argc > 6 ? atoi(argv[6]) : 1;
    if (getenv("DEBUGW")) debugw = 1;
    if (getenv("COUNTONLY")) countonly = 1;
    setup_Mtab();
    for (int k = 0; k <= d - 2; k++) phi[k] = malloc(2 * (1 << (2 * k)));
    phi[0][0] = 0; y[0] = 0;
    FILE *f = fopen(ebfile, "r"); char line[4096]; long idx = 0;
    clock_t T0 = clock();
    while (fgets(line, sizeof line, f)) {
        long my = idx++;
        if (my % nsl != slice) continue;
        int k = atoi(line);
        if (k != kb) { fprintf(stderr, "E_B dim %d != %d\n", k, kb); return 1; }
        char *p = strchr(line, ' ') + 1; p = strchr(p, ' ') + 1; p = strchr(p, ' ') + 1;
        for (int r = 0; r < kb; r++) { char t[9]; memcpy(t, p + 16 * r, 8); t[8] = 0; Eb[r].a = strtoul(t, 0, 16); memcpy(t, p + 16 * r + 8, 8); Eb[r].b = strtoul(t, 0, 16); }
        ebindex = my;
        long cf0 = ncanonfr;
        setup_V2();
        setup_bitsets();
        y[0] = 0;
        /* level 1 starts from y_0 = 0: y_1 >= 1 */
        dfs(1);
        if (countonly) { char *q = strchr(line, ' ') + 1; q = strchr(q, ' ') + 1; char autstr[64]; sscanf(q, "%63s", autstr); fprintf(fout, "%ld %ld %s\n", my, ncanonfr - cf0, autstr); fflush(fout); }
    }
    fclose(fout);
    if (debugw) fprintf(stderr, "DEBUGW: weight-d support lists differing in %ld frames\n", nwdiff);
    fprintf(stderr, "n=%d d=%d slice %d/%d: leaves %ld canonical frames %ld ties %ld nauty %ld accepted %ld out %ld; time %.1fs (acceptance %.1fs)\n",
            n, d, slice, nsl, nleaf, ncanonfr, ntie, nnauty, naccept, nout, (double)(clock() - T0) / CLOCKS_PER_SEC, tAcc / CLOCKS_PER_SEC);
    return 0;
}
