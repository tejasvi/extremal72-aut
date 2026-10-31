# Build a counting variant of lwe11.c: counts lh_check_g calls per level, identity-element calls, components compared.
import sys
s = open(sys.argv[1]).read()
s = s.replace("static int lh_check_g(int g, int t) {      // components 1..r-1, lexicographic; 1 = transported key smaller (prune)\n    for (int i = 1; i < LHr; i++) {",
"static long long CG[42], CGid[42], CGcomp[42], CGprune[42], LHcalls[42], LHnewtr[42]; static int GID = -1;\nstatic int lh_check_g(int g, int t) {      // components 1..r-1, lexicographic; 1 = transported key smaller (prune)\n    CG[t]++; if (g == GID) CGid[t]++;\n    for (int i = 1; i < LHr; i++) { CGcomp[t]++;")
s = s.replace("        if (x < y) return 1;\n        if (x > y) return 0;\n    }\n    return 0;\n}", "        if (x < y) { CGprune[t]++; return 1; }\n        if (x > y) return 0;\n    }\n    return 0;\n}")
s = s.replace("static int lh_reject(int t) {\n    int lv0 = C[LHc0].lv;", "static int lh_reject(int t) {\n    LHcalls[t]++;\n    int lv0 = C[LHc0].lv;")
s = s.replace("            a = (u == 0) ? s0 : tr16(&LHut[(size_t)u * 16], LHm0, syn_ep(cu));", "            a = (u == 0) ? s0 : tr16(&LHut[(size_t)u * 16], LHm0, syn_ep(cu)); LHnewtr[t]++;")
s = s.replace('    if (CHECK) fprintf(stderr, "LWE11CHECK passed', '''    for (int g = 0; g < LHnG && LH && LHr > 1; g++) { int triv = 1; for (int i = 1; i < LHr; i++) { size_t o = (size_t)g * (LHr - 1) + (i - 1); if (LHgc[o] != LHc[i]) triv = 0; for (int j = 0; j < LHm[i]; j++) if (LHgt[o * 16 + j] != (1u << j)) triv = 0; } if (triv) fprintf(stderr, "identity-like g %d\\n", g); }
    for (int t = 0; t <= NLEV; t++) if (LHcalls[t]) fprintf(stderr, "L%d lh calls %lld newtr %lld checkg %lld (id %lld) comps %lld cgprune %lld lhprune %lld\\n", t, LHcalls[t], LHnewtr[t], CG[t], CGid[t], CGcomp[t], CGprune[t], lhprune[t]);
    if (CHECK) fprintf(stderr, "LWE11CHECK passed''')
open(sys.argv[2], 'w').write(s)
