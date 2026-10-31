/* check sampled codes (lines: 12 or n/2 rows %08x%08x ...) against class keys from frames outputs */
#include "cform.h"
int main(int argc, char **argv) {
    int n = atoi(argv[1]), d = atoi(argv[2]); int k = n / 2;
    /* keys from files argv[4..] */
    static f4v keys[200000][12]; long nk = 0; char line[16384];
    for (int a = 4; a < argc; a++) { FILE *f = fopen(argv[a], "r"); while (fgets(line, sizeof line, f)) { for (int r = 0; r < k; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; keys[nk][r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); keys[nk][r].b = strtoul(t, 0, 16); } nk++; } fclose(f); }
    FILE *f = fopen(argv[3], "r"); long tested = 0, miss = 0;
    while (fgets(line, sizeof line, f)) {
        f4v gen[12]; for (int r = 0; r < k; r++) { char t[9]; memcpy(t, line + 16 * r, 8); t[8] = 0; gen[r].a = strtoul(t, 0, 16); memcpy(t, line + 16 * r + 8, 8); gen[r].b = strtoul(t, 0, 16); }
        f4v key[12]; double a; int sc;
        canon_class(gen, k, n, d, key, &a, &sc);
        tested++;
        int found = 0; for (long j = 0; j < nk; j++) if (!mat_cmp(keys[j], key, k)) { found = 1; break; }
        if (!found) { miss++; if (miss <= 3) { printf("missing aut=%.0f sc=%d: ", a, sc); for (int r = 0; r < k; r++) printf("%08x%08x", gen[r].a, gen[r].b); printf("\n"); } }
    }
    printf("tested %ld missing %ld\n", tested, miss);
    return 0;
}
