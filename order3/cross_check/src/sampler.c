/* sampler.c -- own uniform sampler of Hermitian self-dual [24,12] codes over F4 (successive uniform isotropic
   vectors in V^perp \ V), d = 8 test and support invariant (codeinfo.h), membership of the invariant in the
   sorted cls24 invariant list.  usage: sampler SEED NSAMPLES SORTED_INV.bin [OUTMISS]
   prints totals: samples, d=8 count, found, missing (missing codes written to OUTMISS in layout B) */
#include "codeinfo.h"
static uint64_t rs;
static uint64_t rnd(void) { rs += 0x9e3779b97f4a7c15ULL; uint64_t z = rs; z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL; z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL; return z ^ (z >> 31); }
static uint64_t *inv; static size_t ninv;
static int member(uint64_t h) { size_t lo = 0, hi = ninv; while (lo < hi) { size_t m = (lo + hi) / 2; if (inv[m] < h) lo = m + 1; else hi = m; } return lo < ninv && inv[lo] == h; }
/* Hermitian dual of span(V) (k rows) as rows, returns dimension */
static int hdual(const v24 *V, int k, v24 *out) {
    v24 c[24]; for (int t = 0; t < k; t++) c[t] = vconj(V[t]);
    int ord[24]; for (int i = 0; i < 24; i++) ord[i] = i;
    int piv[24]; int r = f4_rref(c, k, ord, 24, piv);
    uint32_t pm = 0; for (int t = 0; t < r; t++) pm |= 1u << piv[t];
    int nd = 0;
    for (int f = 0; f < 24; f++) if (!((pm >> f) & 1)) {
        v24 x = { 1u << f, 0 };
        for (int t = 0; t < r; t++) { int s = vget(c[t], f); if (s) { if (s & 1) x.a |= 1u << piv[t]; if (s & 2) x.b |= 1u << piv[t]; } }
        out[nd++] = x;
    }
    return nd;
}
static int inspan(const v24 *V, int k, v24 x) {   /* x in span(V)? */
    v24 c[25]; memcpy(c, V, sizeof(v24) * (size_t)k); c[k] = x;
    int ord[24]; for (int i = 0; i < 24; i++) ord[i] = i; int piv[25];
    return f4_rref(c, k + 1, ord, 24, piv) == k;
}
int main(int argc, char **argv) {
    rs = strtoull(argv[1], 0, 10) * 1000003ULL + 99;
    long ns = atol(argv[2]);
    FILE *fi = fopen(argv[3], "rb"); fseek(fi, 0, SEEK_END); ninv = (size_t)ftell(fi) / 8; fseek(fi, 0, SEEK_SET);
    inv = malloc(8 * ninv); if (fread(inv, 8, ninv, fi) != ninv) return 1; fclose(fi);
    FILE *fm = argc > 4 ? fopen(argv[4], "w") : NULL;
    static codeinfo ci;
    FILE *fdump = getenv("DUMPFOUND") ? fopen(getenv("DUMPFOUND"), "w") : NULL; long ndump = 0, maxdump = getenv("MAXDUMP") ? atol(getenv("MAXDUMP")) : 2000;
    long nd8 = 0, nfound = 0, nmiss = 0, hist[25] = { 0 };
    for (long s = 0; s < ns; s++) {
        v24 V[12]; int k = 0;
        while (k < 12) {
            v24 D[24]; int nd = hdual(V, k, D);
            v24 x;
            do {
                x.a = x.b = 0;
                for (int t = 0; t < nd; t++) { int c = (int)(rnd() & 3); if (c) x = vadd(x, vscal(D[t], c)); }
            } while ((vwt(x) & 1) || viszero(x) || inspan(V, k, x));
            V[k++] = x;
        }
        codeinfo_analyse(&ci, V);
        if (!ci.ok_so || ci.rank != 12) { fprintf(stderr, "sampler produced a non-self-dual code\n"); return 2; }
        if (ci.dmin_ok != 1) { hist[0]++; continue; }
        nd8++;
        if (member(ci.inv)) {
            nfound++;
            if (fdump && ndump < maxdump) { for (int t = 0; t < 12; t++) fprintf(fdump, "%08x%08x", ci.g[t].a, ci.g[t].b); fprintf(fdump, " 0 %d 0 0 inv=%016llx\n", 3 * ci.nw8, (unsigned long long)ci.inv); ndump++; }
        }
        else {
            nmiss++;
            if (fm) { for (int t = 0; t < 12; t++) fprintf(fm, "%08x%08x", ci.g[t].a, ci.g[t].b); fprintf(fm, " A8=%d\n", 3 * ci.nw8); fflush(fm); }
        }
    }
    printf("samples %ld d8 %ld found %ld missing %ld\n", ns, nd8, nfound, nmiss);
    if (fdump) fclose(fdump);
    return 0;
}
