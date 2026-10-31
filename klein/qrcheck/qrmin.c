// Minimum weight of a binary [n, n/2] code given by two standard-form generator matrices on disjoint information
// sets (rows as 128-bit hex).  Enumerates all combinations of at most T rows of each matrix.  Every codeword of
// weight <= 2T+1 has at most T ones on one of the two information sets, so it is visited.  Also counts the words
// of weight D = 2T+2 exactly: enumeration 1 with at most T+1 rows plus enumeration 2 with at most T rows (a word
// of weight D with a ones on set 1 is counted in pass 1 iff a <= T+1 and in pass 2 iff D-a <= T, i.e. once).
// Usage: qrmin FILE T
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int n, k, T; static u128 G[2][64];
static long long hist[2][129]; static long long visited[2];
static inline int wt(u128 v) { return __builtin_popcountll((uint64_t)v) + __builtin_popcountll((uint64_t)(v >> 64)); }
static void rec(int m, int start, int depth, int maxd, u128 acc) {
    if (depth > 0) { visited[m]++; hist[m][wt(acc)]++; }
    if (depth == maxd) return;
    for (int i = start; i < k; i++) rec(m, i + 1, depth + 1, maxd, acc ^ G[m][i]);
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); T = atoi(argv[2]);
    if (fscanf(f, "%d %d", &n, &k) != 2) return 1;
    for (int m = 0; m < 2; m++) for (int i = 0; i < k; i++) {
        char hx[64]; if (fscanf(f, "%63s", hx) != 1) return 1;
        u128 v = 0; for (char *q = hx; *q; q++) { int d = (*q <= '9') ? *q - '0' : ((*q | 32) - 'a' + 10); v = (v << 4) | (u128)d; }
        G[m][i] = v;
    }
    rec(0, 0, 0, T + 1, 0); rec(1, 0, 0, T, 0);
    int D = 2 * T + 2, minw = 999;
    for (int m = 0; m < 2; m++) for (int w = 1; w <= 2 * T + 1; w++) if (hist[m][w] && w < minw) minw = w;
    printf("n %d k %d T %d: visited %lld + %lld; words of weight <= %d found: %s\n", n, k, T, visited[0], visited[1],
           2 * T + 1, minw == 999 ? "none" : "YES");
    if (minw != 999) printf("minimum weight %d\n", minw);
    printf("A_%d = %lld\n", D, hist[0][D] + hist[1][D]);
    return 0;
}
