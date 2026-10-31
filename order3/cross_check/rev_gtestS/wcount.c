/* count words (not supports) of weight 8,10,12 via sd_lowwords, and max per-line buffer use */
#include "f4code.h"
static long cnt[25];
static void cb(f4v w, int nr, void *c) { int wt = f4wt(w); if (wt <= 12) cnt[wt]++; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[8192]; long ln = 0;
    long mx[25] = {0};
    while (fgets(line, sizeof line, f)) {
        f4v gen[12];
        for (int i = 0; i < 12; i++) { char t[9]; memcpy(t, line + 16 * i, 8); t[8] = 0; gen[i].a = strtoul(t, 0, 16); memcpy(t, line + 16 * i + 8, 8); gen[i].b = strtoul(t, 0, 16); }
        memset(cnt, 0, sizeof cnt);
        sd_lowwords(gen, 24, 12, cb, NULL);
        for (int w = 0; w <= 12; w++) if (cnt[w] > mx[w]) mx[w] = cnt[w];
        if (argc > 2) printf("line %ld A8=%ld A10=%ld A12=%ld | %s", ln, cnt[8], cnt[10], cnt[12], line + 193);
        ln++;
    }
    printf("lines %ld max A8=%ld A10=%ld A12=%ld\n", ln, mx[8], mx[10], mx[12]);
    return 0;
}
