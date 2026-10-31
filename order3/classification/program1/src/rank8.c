/* rank of the weight-8 words for each code in a file (key aut A8 sc idx lines) */
#include "f4code.h"
typedef struct { f4v w[4096]; int n; } wl_t;
static void cb(f4v x, int nr, void *c) { wl_t *L = (wl_t *)c; if (f4wt(x) == 8 && L->n < 4096) L->w[L->n++] = x; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[1024]; long nc = 0, bad = 0;
    static wl_t L;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12]; for (int r = 0; r < 12; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        L.n = 0; sd_lowwords(gen, 24, 8, cb, &L);
        f4v R[16]; int r = 0;
        for (int j = 0; j < L.n && r < 12; j++) { R[r] = L.w[j]; if (f4rank(R, r + 1, 24) == r + 1) r++; }
        nc++; if (r < 12) { bad++; if (bad <= 5) printf("rank %d: %s", r, line); }
    }
    printf("codes %ld, weight-8 words not spanning: %ld\n", nc, bad);
    return 0;
}
