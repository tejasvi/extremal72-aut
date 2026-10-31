#!/bin/sh
# Regenerated on 2026-10-24 with the second program (../bin/rglue, built by ../build.sh). Exit status 0 means
# that no CFCHECK mismatch (exit 9) and no DEBUGW failure (exit 7) occurred.
# Every 1000th code E_B of ../full/E_B_L5.txt (46 codes E_B), with an id= field that keeps the E_B index:
awk 'NR%1000==1 {printf "%s id=%d\n", $0, NR-1}' ../full/E_B_L5.txt > sample46.txt
CFCHECK=1 ../bin/rglue 16 8 sample46.txt out46.txt
# The codes E_B with ids 0 to 7:
awk 'NR<=8 {printf "%s id=%d\n", $0, NR-1}' ../full/E_B_L5.txt > sample8.txt
DEBUGW=1 ../bin/rglue 16 8 sample8.txt out8.txt
# In the shipped copies of out46.txt.eb and out8.txt.eb the last field of each line (seconds) was removed.
