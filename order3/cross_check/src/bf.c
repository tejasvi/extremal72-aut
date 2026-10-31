/* bf.c -- brute-force weight distribution of [24,12] F4 codes (all 4^12 words), for testing. */
#include "f4a.h"
static long long A[25];
static v24 G[12];
static void rec(int t, v24 cur) {
    if (t == 12) { A[vwt(cur)]++; return; }
    for (int s = 0; s < 4; s++) rec(t + 1, s ? vadd(cur, vscal(G[t], s)) : cur);
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[8192]; int maxn = argc > 2 ? atoi(argv[2]) : 1000000, n = 0;
    while (fgets(line, sizeof line, f) && n < maxn) {
        if (!parse_rows_B(line, G, 12)) continue;
        memset(A, 0, sizeof A); v24 z = {0,0}; rec(0, z);
        printf("%d:", n); for (int w = 0; w <= 24; w++) if (A[w]) printf(" %d:%lld", w, A[w]); printf("\n"); n++;
    }
    return 0;
}
