#!/bin/sh
# Regenerated on 2026-10-24: Monte Carlo mass check of the four levels of stage (i) (codes E_B of length 16,
# dimension k = 2..5, minimum distance >= 8), 10^7 samples per level, seed 20261024; then level k = 4 again
# with 10^8 samples and seed 20261025.
# Build first, in this directory: gcc -O3 -march=native -o tisample ../src/tisample.c -lm
for k in 2 3 4 5; do ./tisample 16 $k 8 10000000 20261024 ../eb/n24.L$k.txt; done > tisample.out
./tisample 16 4 8 100000000 20261025 ../eb/n24.L4.txt > tisample_L4_1e8.out
