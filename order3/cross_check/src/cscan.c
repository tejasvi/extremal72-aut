/* cscan.c -- independent scan of a code list in c3class layout (192 hex + "aut A8 selfconj ebindex").
   usage: cscan FILE(.gz) NSHARD SHARD OUTPREFIX
   Writes OUTPREFIX.inv (uint64 invariant per processed line, in order), OUTPREFIX.exc (exceptions, with the
   input line), OUTPREFIX.hist (histograms), OUTPREFIX.log. */
#include <zlib.h>
#include "codeinfo.h"

typedef struct { int a8; unsigned long long aut; int sc; long long cnt; } hent;
static hent H1[4096], H2[4096]; static int nH1 = 0, nH2 = 0;
static void hadd(hent *H, int *n, int a8, unsigned long long aut, int sc) {
    for (int i = 0; i < *n; i++) if (H[i].a8 == a8 && H[i].aut == aut && H[i].sc == sc) { H[i].cnt++; return; }
    H[*n].a8 = a8; H[*n].aut = aut; H[*n].sc = sc; H[*n].cnt = 1; (*n)++;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    gzFile f = gzopen(argv[1], "rb");
    if (!f) { perror("gzopen"); return 1; }
    gzbuffer(f, 1 << 20);
    long NS = atol(argv[2]), SH = atol(argv[3]);
    char fn[4096];
    snprintf(fn, sizeof fn, "%s.inv", argv[4]); FILE *finv = fopen(fn, "wb");
    snprintf(fn, sizeof fn, "%s.exc", argv[4]); FILE *fexc = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s.hist", argv[4]); FILE *fh = fopen(fn, "w");
    snprintf(fn, sizeof fn, "%s.log", argv[4]); FILE *flog = fopen(fn, "w");
    if (!finv || !fexc || !fh || !flog) { perror("open"); return 1; }
    static char line[8192];
    static codeinfo ci;
    long idx = -1, done = 0;
    long cnt_err = 0, cnt_a8 = 0, cnt_r8 = 0, cnt_nd = 0, cnt_aut = 0, cnt_sc = 0, cnt_disc = 0, cnt_cert = 0;
    while (gzgets(f, line, sizeof line)) {
        idx++;
        if (idx % NS != SH) continue;
        size_t L = strlen(line); while (L && (line[L-1] == '\n' || line[L-1] == '\r')) line[--L] = 0;
        v24 rows[12];
        const char *p = parse_rows_B(line, rows, 12);
        unsigned long long aut = 0; int a8 = -1, sc = -1, eb = -1;
        if (!p || sscanf(p, "%llu %d %d %d", &aut, &a8, &sc, &eb) != 4) { fprintf(fexc, "%ld PARSE | %s\n", idx, line); cnt_err++; uint64_t z = 0; fwrite(&z, 8, 1, finv); done++; continue; }
        int rc = codeinfo_analyse(&ci, rows);
        int hard = (rc < 0) || !ci.ok_so || ci.rank < 12 || ci.dmin_ok != 1;
        if (hard) { fprintf(fexc, "%ld HARD so=%d rank=%d dmin=%d rc=%d | %s\n", idx, ci.ok_so, ci.rank, ci.dmin_ok, rc, line); cnt_err++; uint64_t z = 0; fwrite(&z, 8, 1, finv); done++; continue; }
        fwrite(&ci.inv, 8, 1, finv);
        int myA8 = 3 * ci.nw8;
        hadd(H1, &nH1, a8, aut, sc);   /* fields as given */
        int flag = 0;
        if (myA8 != a8) { flag = 1; cnt_a8++; fprintf(fexc, "%ld A8 mine=%d field=%d | %s\n", idx, myA8, a8, line); }
        if (ci.rank8 < 12) { cnt_r8++; fprintf(fexc, "%ld R8 rank8=%d aut=%llu | %s\n", idx, ci.rank8, aut, line); }
        if (!ci.connected || !ci.covers) { cnt_disc++; fprintf(fexc, "%ld DISC conn=%d cov=%d | %s\n", idx, ci.connected, ci.covers, line); }
        if (ci.aut3_cert) {
            cnt_cert++;
            if (aut != 3) { flag = 1; cnt_aut++; fprintf(fexc, "%ld AUT cert3 field=%llu | %s\n", idx, aut, line); }
            if (ci.selfconj != sc) { flag = 1; cnt_sc++; fprintf(fexc, "%ld SC mine=%d field=%d | %s\n", idx, ci.selfconj, sc, line); }
            if (!flag) hadd(H2, &nH2, myA8, 3ULL, ci.selfconj);
        } else {
            cnt_nd++;
            fprintf(fexc, "%ld ND ncol=%d aut=%llu | %s\n", idx, ci.ncolors, aut, line);
        }
        done++;
        if (done % 100000 == 0) { fprintf(flog, "done %ld idx %ld\n", done, idx); fflush(flog); fflush(fexc); }
    }
    fprintf(fh, "# processed %ld errors %ld A8mismatch %ld rank8lt12 %ld nondiscrete %ld cert3 %ld autmismatch %ld scmismatch %ld disconnected %ld\n",
            done, cnt_err, cnt_a8, cnt_r8, cnt_nd, cnt_cert, cnt_aut, cnt_sc, cnt_disc);
    fprintf(fh, "# FIELDS histogram: a8 aut sc count\n");
    for (int i = 0; i < nH1; i++) fprintf(fh, "F %d %llu %d %lld\n", H1[i].a8, H1[i].aut, H1[i].sc, H1[i].cnt);
    fprintf(fh, "# VERIFIED (cert3) histogram: a8 aut sc count\n");
    for (int i = 0; i < nH2; i++) fprintf(fh, "V %d %llu %d %lld\n", H2[i].a8, H2[i].aut, H2[i].sc, H2[i].cnt);
    fprintf(flog, "FINISHED done %ld last idx %ld\n", done, idx);
    fclose(finv); fclose(fexc); fclose(fh); fclose(flog); gzclose(f);
    return 0;
}
