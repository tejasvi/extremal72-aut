#!/bin/bash
# Planted positive control for csp5p in the production environment (audit request, 2026-10-21).
# Inputs were built OFFLINE by csp5p_plantdump (frozen csp5p.c + DUMPF): forbidden 8-/12-set bitmaps of three real
# cls24 classes (ids 1234567, 6543210, 10987654), each once with a planted labelled Golay code cleared (PLANT applied
# at build time; full count at build time found exactly 1 labelling = the planted one) and once unplanted.
# This run uses NO environment variables: the box's production binary and block file, csp5p F mode.
# Expected: planted -> SAT, hash = planted hash, verified=1/1; unplanted -> UNSAT with the production node count.
# usage: bash run_control.sh D     (D = the box's production directory with kit/ and tmp/)
set -u
D=$1; cd "$(dirname "$0")"
export TMPDIR=$D/tmp
sha256sum -c --quiet SHA256SUMS || { echo "CONTROL_FAIL: input checksum"; exit 2; }
echo "host $(hostname); binary+blocks sha256: $(sha256sum $D/kit/csp5p_static_v3 $D/kit/octdod.txt | cut -c1-64 | tr '\n' ' ')"
echo "env hits (STOP16/PLANT/NOQ/COUNT/VERBOSE): $(env | grep -cE '^(STOP16|PLANT|NOQ|COUNT|VERBOSE)=')"
for x in $(cat instances.txt); do nice -n 10 $D/kit/csp5p_static_v3 24 F ${x}_f8.bin ${x}_f12.bin $D/kit/octdod.txt 2>/dev/null; done > results.txt
if sed -E 's/ wall=[0-9.]+ cpu=[0-9.]+ prep=[0-9.]+//' results.txt | diff - EXPECTED.txt > diff.txt; then echo CONTROL_PASS
else echo CONTROL_FAIL; cat diff.txt; fi
cut -c1-120 results.txt
