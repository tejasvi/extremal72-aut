/* symchk: for given class-list lines, recompute exactly what the production binary (gtestS_prod.c = 97be159f)
   did at level 1 with the symmetry reduction: root 5-set F0 (choose_root), nauty generators of the graph on the
   weight-8 words with F0 as a separate cell (compute_l1_orbits), and check whether every generator maps the
   sets of supports of weight 8, 10 and 12 of E onto themselves (then the group preserves the forbidden sets).
   Usage: symchk file   (every line of file is a class-list line) */
#define main gtestS_main
#include "../gtestS_prod.c"
#undef main
static int in_set(const uint32_t *s, int n, uint32_t x) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (s[m] == x) return 1; if (s[m] < x) lo = m + 1; else hi = m - 1; }
    return 0;
}
static long bad_images(const uint32_t *s, int n, const int *p) {
    long b = 0; for (int i = 0; i < n; i++) if (!in_set(s, n, applyperm(p, s[i]))) b++;
    return b;
}
int main(int argc, char **argv) {
    gcore_init();
    { int k = 0; for (uint32_t p = 0; p < 4096; p++) if (__builtin_popcount(p) == 4) { idx4_12[p] = k; pat4_12[k++] = p; } }
    init_closures();
    { int k = 0; for (uint32_t p = 0; p < 65536; p++) if (__builtin_popcount(p) == 4) { zidx16[p] = k; zpat16[k++] = p; } }
    { int k = 0; for (int i = 0; i < 16; i++) for (int j = i + 1; j < 16; j++) { pairidx[i][j] = pairidx[j][i] = k++; } }
    { int k = 0; for (uint32_t p = 0; p < (1u << 24); p++) if (__builtin_popcount(p) == 5) all5[k++] = p; }
    FILE *f = fopen(argv[1], "r"); char line[8192]; int ln = 0;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12]; if (!parse_code_line(line, gen)) continue;
        curgen = gen; use_incidence = 1;
        set_forbidden_from_E(gen);
        build_indexes();
        resetK();
        int rc; uint32_t F0 = choose_root(&rc, 0);
        use_sym = 1; compute_l1_orbits(F0);
        long b8 = 0, b10 = 0, b12 = 0; int nontriv = 0;
        for (int g = 0; g < nsgen; g++) {
            int id = 1; for (int i = 0; i < 24; i++) if (sgen[g][i] != i) id = 0;
            nontriv += !id;
            b8 += bad_images(E_s8, E_n8, sgen[g]); b10 += bad_images(E_s10, E_n10, sgen[g]); b12 += bad_images(E_s12, E_n12, sgen[g]);
        }
        int norb = 0; for (int i = 0; i < 969; i++) norb += l1rep[i];
        printf("line %d: F0=%06x allowed-through=%d generators=%d (non-identity %d) orbits(all 969)=%d orbits(allowed)=%ld "
               "supports n8=%d n10=%d n12=%d; images outside the set: w8 %ld w10 %ld w12 %ld\n",
               ln, F0, rc, nsgen, nontriv, norb, nl1orb, E_n8, E_n10, E_n12, b8, b10, b12);
        ln++;
    }
    return 0;
}
