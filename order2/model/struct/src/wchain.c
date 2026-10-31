// wchain: beam search over WORD CHAINS (syndrome-span orders) for the C2 level-wise search.
// A state is a subspace S of the 119-dim space of gauge-invariant functionals (syndrome forms), kept in fully
// reduced row echelon form (pivot = top bit).  A word z is FREE (checkable) iff all its syndrome forms lie in S.
// Heuristic log2 nodes of a state = dim S - sum_{z free} L_z (L_z = -log2 pass probability), as for flags.
// A move adds the forms of one candidate word y: delta = rank(forms(y) mod S) new dims; newly free words are the
// non-free z with forms(z) in S + forms(y).  Score of a chain = log2 sum over its steps of 2^(log2 nodes).
// Beam: buckets indexed by dim; each bucket keeps the BEAM best states (by score), deduplicated by subspace.
// Usage: wchain WORDSFILE BEAM [CANDWEIGHTS e.g. 8,10] [FORCE y1,y2,...]   (env TOPK: candidates kept per state)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128;
typedef uint64_t u64;
#define MAXW 12000
#define MAXF 11
static int NV, NW; static int wt[MAXW], nf[MAXW]; static double Lw[MAXW]; static u64 wy[MAXW];
static u128 fm[MAXW][MAXF];
static inline int topbit(u128 v) { u64 hi = (u64)(v >> 64); return hi ? 127 - __builtin_clzll(hi) : 63 - __builtin_clzll((u64)v); }
typedef struct {
    int dim; u128 pivmask; u128 piv[128];
    u64 fr[(MAXW + 63) / 64];
    double L, score, peak; int nstep; int path[128]; unsigned char pd[128]; float pln[128]; int pfree[128];
    u64 hash; int nfree;
} State;
static inline u128 red(const State *s, u128 v) {
    u128 m = v & s->pivmask;
    while (m) { int p = topbit(m); v ^= s->piv[p]; m = v & s->pivmask; }
    return v;
}
static void addvec(State *s, u128 r) {   // r already reduced mod s, nonzero
    int p = topbit(r);
    for (int q = 0; q < 128; q++) if (((s->pivmask >> q) & 1) && ((s->piv[q] >> p) & 1)) s->piv[q] ^= r;
    s->piv[p] = r; s->pivmask |= ((u128)1) << p; s->dim++;
}
static u64 mix(u128 v) { u64 a = (u64)v, b = (u64)(v >> 64); a ^= b * 0x9E3779B97F4A7C15ULL; a ^= a >> 31; a *= 0xBF58476D1CE4E5B9ULL; a ^= a >> 29; return a; }
static u64 shash(const State *s) { u64 h = 0; for (int q = 0; q < 128; q++) if ((s->pivmask >> q) & 1) h += mix(s->piv[q]) ^ (u64)q; return h; }
// small RREF in the quotient: basis vectors b[0..n-1] with pivots
typedef struct { int n; u128 b[MAXF]; u128 pm; } Small;
static inline void small_add(Small *S, u128 v) {
    for (int i = 0; i < S->n; i++) { int p = topbit(S->b[i]); if ((v >> p) & 1) v ^= S->b[i]; }
    if (!v) return;
    int p = topbit(v);
    for (int i = 0; i < S->n; i++) if ((S->b[i] >> p) & 1) S->b[i] ^= v;
    S->b[S->n++] = v; S->pm |= ((u128)1) << p;
}
static inline int small_contains(const Small *S, u128 v) {
    for (int i = 0; i < S->n; i++) { int p = topbit(S->b[i]); if ((v >> p) & 1) v ^= S->b[i]; }
    return v == 0;
}
static double lse2(double a, double b) { double m = a > b ? a : b; return m + log2(exp2(a - m) + exp2(b - m)); }
static int candw[64]; static int ncandw = 0;
static int iscand(int w) { for (int i = 0; i < ncandw; i++) if (candw[i] == w) return 1; return 0; }
// per-state scratch
static Small Rz[MAXW]; static int nonfree[MAXW];
typedef struct { int y; int delta; double gain; double ln; int nnew; } Move;
static int cmpmove(const void *a, const void *b) { const Move *x = a, *y = b; return (x->ln > y->ln) - (x->ln < y->ln); }
// apply move y to state s -> ns
static void apply(const State *s, State *ns, int y) {
    *ns = *s;
    Small R = {0};
    for (int k = 0; k < nf[y]; k++) small_add(&R, red(s, fm[y][k]));
    for (int i = 0; i < R.n; i++) { u128 r = red(ns, R.b[i]); if (r) addvec(ns, r); }
    int nn = 0; double g = 0;
    for (int z = 0; z < NW; z++) {
        if ((ns->fr[z >> 6] >> (z & 63)) & 1) continue;
        int ok = 1; for (int k = 0; k < nf[z] && ok; k++) if (red(ns, fm[z][k])) ok = 0;
        if (ok) { ns->fr[z >> 6] |= 1ULL << (z & 63); g += Lw[z]; nn++; }
    }
    ns->L += g; ns->nfree += nn;
    double ln = ns->dim - ns->L;
    ns->score = (s->nstep == 0) ? ln : lse2(s->score, ln);
    ns->peak = (s->nstep == 0 || ln > s->peak) ? ln : s->peak;
    ns->path[ns->nstep] = y; ns->pd[ns->nstep] = (unsigned char)ns->dim; ns->pln[ns->nstep] = (float)ln; ns->pfree[ns->nstep] = nn; ns->nstep++;
    ns->hash = shash(ns);
}
typedef struct { int pb, ps; int y; double score, peak; u64 hash; int dim; } Rec;
static u64 move_hash(const State *s, int y, int *ndim) {
    State t; t.pivmask = s->pivmask; memcpy(t.piv, s->piv, sizeof t.piv); t.dim = s->dim;
    for (int k = 0; k < nf[y]; k++) { u128 r = red(&t, fm[y][k]); if (r) addvec(&t, r); }
    *ndim = t.dim; return shash(&t);
}
static inline double rkey(int OBJ, double score, double peak) { return OBJ ? peak * 1000 + score : score; }
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d %d", &NV, &NW) != 2 || NW > MAXW || NV > 128) return 1;
    for (int z = 0; z < NW; z++) {
        unsigned long long y;
        if (fscanf(f, "%d %lf %d %llu", &wt[z], &Lw[z], &nf[z], &y) != 4 || nf[z] > MAXF) return 2;
        wy[z] = y;
        for (int k = 0; k < nf[z]; k++) { char hx[64]; if (fscanf(f, "%63s", hx) != 1) return 3;
            u128 v = 0; for (char *q = hx; *q; q++) { int dv = (*q <= '9') ? *q - '0' : ((*q | 32) - 'a' + 10); v = (v << 4) | (u128)dv; } fm[z][k] = v; }
    }
    fclose(f);
    int BEAM = atoi(argv[2]);
    if (argc > 3) { char *t = strtok(argv[3], ","); while (t) { candw[ncandw++] = atoi(t); t = strtok(NULL, ","); } } else { candw[0] = 8; candw[1] = 10; ncandw = 2; }
    int TOPK = getenv("TOPK") ? atoi(getenv("TOPK")) : 16;
    int OBJ = getenv("OBJPEAK") ? 1 : 0;      // 0: rank by score (total), 1: by peak then score
    int W = 12;                                // window of materialized buckets (max delta 11)
    State **mat = malloc(sizeof(State *) * W); int *mn = calloc(W, sizeof(int));
    for (int i = 0; i < W; i++) mat[i] = malloc(sizeof(State) * (size_t)BEAM);
    Rec **rb = malloc(sizeof(Rec *) * 129); int *rn = calloc(129, sizeof(int));
    for (int d = 0; d <= NV; d++) rb[d] = malloc(sizeof(Rec) * (size_t)BEAM);
    State *s0 = calloc(1, sizeof(State)); s0->score = -1e9; s0->peak = -1e9;
    if (argc > 4) {
        char *t = strtok(argv[4], ",");
        while (t) { unsigned long long y = strtoull(t, NULL, 10); int z = -1; for (int q = 0; q < NW; q++) if (wy[q] == y) z = q;
            if (z < 0) { fprintf(stderr, "forced word not found\n"); return 4; }
            State *tmp = malloc(sizeof(State)); apply(s0, tmp, z); *s0 = *tmp; free(tmp); t = strtok(NULL, ","); }
        fprintf(stderr, "forced prefix: dim %d L %.2f ln %.2f\n", s0->dim, s0->L, s0->dim - s0->L);
    }
    int d0 = s0->dim;
    Move *mv = malloc(sizeof(Move) * MAXW);
    for (int d = d0; d < NV; d++) {
        State *M = mat[d % W]; int nM = 0;
        if (d == d0) { M[0] = *s0; nM = 1; }
        else {
            for (int r = 0; r < rn[d]; r++) { Rec *R = &rb[d][r]; apply(&mat[R->pb % W][R->ps], &M[nM], R->y); nM++; }
        }
        mn[d % W] = nM;
        if (!nM) continue;
        int bi = 0; for (int i = 1; i < nM; i++) if (rkey(OBJ, M[i].score, M[i].peak) < rkey(OBJ, M[bi].score, M[bi].peak)) bi = i;
        fprintf(stderr, "dim %d: %d states, best score %.2f peak %.2f ln %.2f free %d steps %d\n", d, nM, M[bi].score, M[bi].peak, M[bi].dim - M[bi].L, M[bi].nfree, M[bi].nstep);
        for (int si = 0; si < nM; si++) {
            State *s = &M[si];
            int nnf = 0;
            for (int z = 0; z < NW; z++) {
                if ((s->fr[z >> 6] >> (z & 63)) & 1) continue;
                Small *R = &Rz[z]; R->n = 0; R->pm = 0;
                for (int k = 0; k < nf[z]; k++) { u128 r = red(s, fm[z][k]); if (r) small_add(R, r); }
                nonfree[nnf++] = z;
            }
            int nm = 0;
            for (int i = 0; i < nnf; i++) {
                int y = nonfree[i]; if (!iscand(wt[y])) continue;
                const Small *Ry = &Rz[y]; double g = 0; int nn = 0;
                for (int j = 0; j < nnf; j++) {
                    int z = nonfree[j]; const Small *R = &Rz[z];
                    if (R->n > Ry->n || (R->pm & ~Ry->pm)) continue;
                    int ok = 1; for (int k = 0; k < R->n && ok; k++) if (!small_contains(Ry, R->b[k])) ok = 0;
                    if (ok) { g += Lw[z]; nn++; }
                }
                mv[nm].y = y; mv[nm].delta = Ry->n; mv[nm].gain = g; mv[nm].nnew = nn;
                mv[nm].ln = (s->dim + Ry->n) - (s->L + g);
                nm++;
            }
            qsort(mv, nm, sizeof(Move), cmpmove);
            int perdelta[16] = {0};
            for (int i = 0; i < nm; i++) {
                if (perdelta[mv[i].delta] >= TOPK) continue;
                perdelta[mv[i].delta]++;
                double sc = (s->nstep == 0) ? mv[i].ln : lse2(s->score, mv[i].ln);
                double pk = (s->nstep == 0 || mv[i].ln > s->peak) ? mv[i].ln : s->peak;
                int nd = s->dim + mv[i].delta; if (nd > NV) continue;
                double key = rkey(OBJ, sc, pk);
                Rec *B = rb[nd]; int n = rn[nd];
                // quick reject if bucket full and worse than worst
                int wq = -1; double wk = -1e300;
                if (n >= BEAM) { for (int q = 0; q < n; q++) { double k2 = rkey(OBJ, B[q].score, B[q].peak); if (k2 > wk) { wk = k2; wq = q; } } if (key >= wk) continue; }
                int dd; u64 h = move_hash(s, mv[i].y, &dd);
                int dup = -1; for (int q = 0; q < n; q++) if (B[q].hash == h) { dup = q; break; }
                Rec rec = { d, si, mv[i].y, sc, pk, h, nd };
                if (dup >= 0) { if (key < rkey(OBJ, B[dup].score, B[dup].peak)) B[dup] = rec; continue; }
                if (n < BEAM) { B[n] = rec; rn[nd] = n + 1; } else B[wq] = rec;
            }
        }
        rn[d] = 0;
    }
    // final bucket NV: materialize best
    int nb = rn[NV]; if (!nb) { fprintf(stderr, "no complete chain\n"); return 5; }
    int bq = 0; for (int q = 1; q < nb; q++) if (rkey(OBJ, rb[NV][q].score, rb[NV][q].peak) < rkey(OBJ, rb[NV][bq].score, rb[NV][bq].peak)) bq = q;
    State *best = malloc(sizeof(State)); apply(&mat[rb[NV][bq].pb % W][rb[NV][bq].ps], best, rb[NV][bq].y);
    printf("SCORE %.3f PEAK %.3f STEPS %d\n", best->score, best->peak, best->nstep);
    printf("CHAIN");
    for (int i = 0; i < best->nstep; i++) printf(" %llu", (unsigned long long)wy[best->path[i]]);
    printf("\nDIMS"); for (int i = 0; i < best->nstep; i++) printf(" %d", best->pd[i]);
    printf("\nLN"); for (int i = 0; i < best->nstep; i++) printf(" %.1f", best->pln[i]);
    printf("\nNEWFREE"); for (int i = 0; i < best->nstep; i++) printf(" %d", best->pfree[i]);
    printf("\nWT"); for (int i = 0; i < best->nstep; i++) printf(" %d", wt[best->path[i]]);
    printf("\n");
    return 0;
}
