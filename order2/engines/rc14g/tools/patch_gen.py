"""patch_gen.py SRC DST : rc13 + hooks for per-package generated lane loops (round 2, direction 3).
 - LWE11GENDUMP=FILE: after the tables are built, write each fast level's lane layout (the generator's input) and exit.
 - Compiled with -DPKGGEN -DPKGGEN_H='"GEN.h"': levels with a generated lane loop (narrow paths, kt <= 8) call it instead of
   the generic loops; GEN.h's gen_check() first verifies that the runtime layout equals the generated constants.
Same decisions and output; LWE11CHECK still checks every fast node.  Exact anchors, each must occur once."""
import sys

src, dst = sys.argv[1], sys.argv[2]
s = open(src).read()


def rep(old, new, cnt=1):
    global s
    n = s.count(old)
    if n != cnt:
        sys.exit(f"anchor found {n} times (want {cnt}): {old[:90]!r}")
    s = s.replace(old, new)


# 1. dump mode and layout check, right after build_fast()
rep("    build_fast();\n",
    "    build_fast();\n"
    "    if (getenv(\"LWE11GENDUMP\")) {         // generator input: lane layout of every fast level\n"
    "        FILE *g = fopen(getenv(\"LWE11GENDUMP\"), \"w\"); if (!g) die(\"open gendump\");\n"
    "        for (int t = 0; t < NLEV; t++) { const LV *L = &LVL[t];\n"
    "            fprintf(g, \"L %d on %d kt %d nz %d vec %d arena %d nr0 %d ntr %d ndir %d nc %d hs %d de %d\\n\", t, L->on, L->kt, L->nz, L->vec, L->arena, L->nr0, L->ntr, L->ndir, L->nc, L->hs, L->de);\n"
    "            for (int i = L->nr0 + L->ntr - L->ndir; i < L->nr0 + L->ntr && L->ndir > 0; i++) fprintf(g, \"D %d %d %u\\n\", t, i, L->DOFF[i]); }\n"
    "        fclose(g); exit(0);\n"
    "    }\n"
    "#ifdef PKGGEN\n"
    "    gen_check();                            // generated constants must equal this run's layout\n"
    "#endif\n")

# 2. narrow paths: generated lane loops first
rep("        u64 w[8] __attribute__((aligned(64))) = {0};\n",
    "        u64 w[8] __attribute__((aligned(64))) = {0};\n"
    "#ifdef PKGGEN\n"
    "        { const int r_ = gen_lanes(t, S, L, w); if (r_ == 0) goto dead; if (r_ > 0) goto gen_done; }\n"
    "#endif\n")
i0 = s.index("        u64 w[8] __attribute__((aligned(64))) = {0};\n")
a = "        for (int i = nr0 + ntr; i < nc; i++) {           // rest: child by child\n"
i1 = s.index(a, i0)
s = s[:i1] + "#ifdef PKGGEN\n        gen_done:\n#endif\n" + s[i1:]

# 3. the generated header goes in after the engine's types, tables and helpers
rep("static void search_fast_wide(LV *L, int t, const uint16_t *S) __attribute__((noinline));\n",
    "#ifdef PKGGEN\n#include PKGGEN_H\n#endif\n"
    "static void search_fast_wide(LV *L, int t, const uint16_t *S) __attribute__((noinline));\n")

open(dst, 'w').write(s)
print(f"patched {src} -> {dst}")
