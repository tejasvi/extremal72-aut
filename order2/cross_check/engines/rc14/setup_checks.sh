#!/bin/bash
# rc14 / rc14g audit, static and start-up checks (audit code, 2026-10-24).  Single core, nice 10, TMPDIR in the audit dir.
# 1 rebuild rc14 and the three rc14g binaries from their frozen sources, compare with the frozen hashes;
# 2 rebuild the source chain: patch_rc14(rc13) = frozen rc14 source; patch_gen(rc14) + generated header = each rc14g source;
# 3 regenerate each package's lane-layout dump with the hooked engine and production inputs, and the header with gen.py;
# 4 layout guard: every rc14g binary on the other packages' instances.
set -u
AL=<HOME>/c72/c2opt/alg; G=$AL/frozen_rc14g; F=<HOME>/c72/fleet/pkgs
W=<HOME>/c72/audit/c2audit/engine-check/rc14; B=$W/build
export TMPDIR=<HOME>/c72/audit/c2audit/tmp OMP_NUM_THREADS=1
ulimit -v 33554432
FL="-pipe -O3 -march=x86-64-v4 -mavx512vbmi -mgfni -mavx512vpopcntdq"
cd $B || exit 1
echo "== 1 rebuild"
mkdir -p rc14 && cp $AL/frozen_rc14/lwe11.c rc14/ && (cd rc14 && nice -n 10 gcc $FL -o lwe11 lwe11.c && echo "rc14 $(sha256sum lwe11 | cut -c1-16) frozen $(sha256sum $AL/frozen_rc14/lwe11 | cut -c1-16)")
for p in y40 y12-lb2 y15-lb; do mkdir -p g_$p && cp $G/$p/lwe11.c g_$p/ && (cd g_$p && nice -n 10 gcc $FL -o lwe11 lwe11.c && echo "rc14g $p $(sha256sum lwe11 | cut -c1-16) frozen $(sha256sum $G/$p/lwe11 | cut -c1-16)"); done
echo "== 2 source chain"
python3 -I $G/tools/patch_rc14.py $AL/frozen_rc13/lwe11.c chain_rc14.c > /dev/null && cmp chain_rc14.c $AL/frozen_rc14/lwe11.c && echo "patch_rc14(rc13) == frozen rc14 source"
python3 -I $G/tools/patch_gen.py $AL/frozen_rc14/lwe11.c chain_hooked.c > /dev/null && echo "hooked source $(sha256sum chain_hooked.c | cut -c1-16)"
for p in y40 y12-lb2 y15-lb; do
  diff chain_hooked.c $G/$p/lwe11.c > d_$p.diff; echo "$p: diff lines < $(grep -c '^<' d_$p.diff)  > $(grep -c '^>' d_$p.diff)"; grep '^[<>]' d_$p.diff | head -4 | cut -c1-150
  python3 -I - "$G/$p/lwe11.c" "$G/tools/gen1m_$p.h" <<'PY'
import sys
s = open(sys.argv[1]).read(); h = open(sys.argv[2]).read()
print('  header text embedded verbatim:', h in s, ' (header', len(h), 'bytes)')
PY
done
echo "== 3 regenerate dumps and headers"
nice -n 10 gcc $FL -o hooked chain_hooked.c || exit 1
for p in y40 y12-lb2 y15-lb; do
  P=$F/$p; ENV="LTSHFILE=$P/sym.ltsh"; [ -f $P/sym.ltsb ] && ENV="$ENV LTSBFILE=$P/sym.ltsb"
  env $ENV LWE11GENDUMP=$B/dump_$p.txt timeout 300 nice -n 10 ./hooked $P/inst.txt 3 64000 0 > /dev/null 2> dumperr_$p.txt; echo "$p dump rc=$? $(cmp -s dump_$p.txt $G/tools/dump1m_$p.txt && echo IDENTICAL to tools/dump1m || echo DIFFERS)"
  python3 -I $G/tools/gen.py dump_$p.txt gen_$p.h > /dev/null && cmp -s gen_$p.h $G/tools/gen1m_$p.h && echo "  gen.py(dump) IDENTICAL to tools/gen1m_$p.h; levels: $(grep -o 'int gen_L[0-9]*' gen_$p.h | tr '\n' ' ')" || echo "  header DIFFERS"
done
echo "== 4 layout guard"
for b in y40 y12-lb2 y15-lb; do for p in y40 y12-lb2 y15-lb y0-lb y14-lb y19b-lb; do
  [ $b = $p ] && continue; P=$F/$p; [ -d $P ] || P=<HOME>/c72/c2opt/struct/runs/$p
  ENV="LTSHFILE=$P/sym.ltsh"; [ -f $P/sym.ltsb ] && ENV="$ENV LTSBFILE=$P/sym.ltsb"
  env $ENV timeout 120 nice -n 10 g_$b/lwe11 $P/inst.txt 3 64000 0 > out.txt 2> err.txt; rc=$?
  echo "rc14g_$b on $p: rc=$rc stdout_lines=$(wc -l < out.txt) $(grep -o 'PKGGEN[^"]*' err.txt | head -1)"
done; done
