# Supplementary material: The automorphism group of an extremal [72,36,16] code is trivial

This archive contains the programs, instance files, logs and certificates of the computations in the paper
"The automorphism group of an extremal [72,36,16] code is trivial". Its Main Theorem states: The automorphism group of a binary doubly-even self-dual [72,36,16] code is trivial.
Earlier work shows that this group is trivial or isomorphic to C2, C3, C2 x C2 or C5, and that its involutions
are fixed-point-free (Sec. 1 of the paper). The Main Theorem therefore follows from Theorems A to D below,
about a putative doubly-even self-dual [72,36,16] code C and about Hermitian self-dual codes over F4.

- Theorem A: C has no automorphism of order 5 (Sec. 2 of the paper).
- Theorem B: C has no automorphism of order 3 (Sec. 4).
- Theorem C: there are 26 924 931 Hermitian self-dual [24,12,8] codes over F4 up to monomial equivalence, and
  13 485 816 up to monomial equivalence and conjugation (Sec. 5).
- Theorem D: C has no fixed-point-free involution; for each of the 41 self-dual [36,18,8] codes Y, no extremal code
  has a fixed-point-free involution with contracted fixed code Y (Sec. 6).
- Proposition 3.8: Aut(C) contains no subgroup C2 x C2. It checks, by a much smaller computation, the case C2 x C2
  that Theorem D also excludes (Sec. 3).

The reductions and the final deduction are also formalized in Lean 4 with Mathlib (directory `lean/`); the formal
proof assumes only results from the literature and the outcomes of the computations for Theorems A to D (see "Lean
formalization").

Where to start: for each of the five results, the main run whose output is used in its proof, the checks made on
it, and one command, run from the top directory, that re-derives its totals from the shipped records. The section
of each result gives the requirements, the expected output and all its checks.

| Result | Main run | Checked by | Command |
|---|---|---|---|
| Theorem A | the order-5 search, 224 jobs | the independent implementation; the 192 five-row nodes re-checked by independently written code | `sh order5/logs/main_run/collect.sh` |
| Theorem B | point placement on the 13 485 816 classes | octad growth on every class; the coverage of both runs checked by two programs each; an independent solver on 5 711 classes | `cd order3/labelling && python3 point_placement/main_run/aggregate.py 13485816 point_placement/main_run/results/host{D,E,C}.out.tgz` |
| Theorem C | the class list | the second classification program; the double count of step (5) | `cd order3/classification && python3 class_list/check_class_list.py class_list/cls24.txt.gz` |
| Theorem D | 41 searches, one per fixed code | independent re-searches of Y8, Y18, Y22, Y23 and Y39; for all 41, partial reruns with the reference program and the coverage checker; the parity certificate of Y39 | `bash order2/cross_check/coverage/run_coverage.sh -o OUT all` |
| Proposition 3.8 | Implementation I on the 119 instances, 560 job outputs | Implementation II, with two basis orders; the third solver on 113 instances; removal certificates | `cd klein && python3 impl1_runs/lw_unique.py impl1_runs` |

Section, table, lemma and proposition numbers below are those of the paper. Table 1 is the order-5 search,
Table 2 the class counts of Theorem C by beta and by automorphism group order, Table 3 the searches of Theorem D, and Table 4 (Sec. 7) summarises the checks of the main runs. The tests of individual components are listed
in the section "Tests of individual components".

## Layout

| Directory | Result | Paper |
|---|---|---|
| `order5/` | Theorem A: the order-5 search with its tests, job logs and cross-checks, and the independent implementation | Sec. 2, Table 1 |
| `klein/` | Proposition 3.8: the 41 codes, the instances, the three search programs with their logs and removal certificates, and the cross-checks | Sec. 3 and 7 |
| `order3/classification/` | Theorem C: the class list and the two classification programs with their tests | Sec. 5 and 7, Table 2 |
| `order3/labelling/` | Theorem B: the two labelling programs with their tests, and the results of both main runs | Sec. 4.3, 4.4 and 7 |
| `order3/reduction/` | Theorem B: the check of the weight formula of Lemma 4.1 on the extended quadratic residue code of length 48 (a component test) | Sec. 4.2 |
| `order2/` | Theorem D: the 41 runs with their inputs, programs, part logs and checks, and the independent re-searches | Sec. 6, Table 3 |
| `order3/cross_check/` | Theorems B and C: the order-3 cross-check and its outputs (see "Checks of Theorem C" and "Checks of Theorem B") | Sec. 7 |
| `lean/` | The formal proof in Lean of the deduction of the Main Theorem (see "Lean formalization") | Sec. 7 |

Version 1 is distributed as four files that unpack into the same directory `extremal72-aut-supplement-v1/`:
`extremal72-aut-supplement-v1-core.tar.gz` (programs, records, the `README.md` of version 1 and the files below),
`extremal72-aut-supplement-v1-instances.tar` (the instance files of `klein/`, already gzip-compressed),
`extremal72-aut-supplement-v1-results.tar` (the per-class results of the point-placement main run) and
`extremal72-aut-supplement-v1-classlist.tar` (the class list). Unpack all four, for example with
`for f in extremal72-aut-supplement-v1-*.tar*; do tar -xf "$f"; done`.

Version 2 adds six files (plus this README as `README_v2.md`). Five of them unpack into
`extremal72-aut-supplement-v1/order2/`: `extremal72-aut-supplement-v2-order2-core.tar.gz` (programs, small records,
reports), `-order2-runs.tar.gz` (part logs and run manifests), `-order2-inputs.tar.gz` (instances and symmetry
files), `-order2-independent.tar.gz` (outputs of the independent re-searches) and `-order2-crosscheck.tar.gz`
(outputs of the coverage checker and the engine cross-checks). `order2/SHA256SUMS` covers the files of these five
parts, and `order2/MODES.txt` lists the modes of the files of `order2/`. The sixth,
`extremal72-aut-supplement-v2-lean.tar.gz`, unpacks into `extremal72-aut-supplement-v1/lean/` (the Lean
formalization); `lean/SHA256SUMS` covers its files.
Sizes: core 17.6 MB, runs 232.7 MB, inputs 61.9 MB, independent 624.2 MB, crosscheck 95.4 MB, lean 0.3 MB.

Files at the top level:

- `README.md`: the README of version 1, unchanged; this file, `README_v2.md`, replaces it.
- `LICENSE` and `LICENSE-DATA`: the licences of the code and of the data (see "Licences").
- `REDACTIONS.tsv`: every file whose bytes differ from the file that was run or written during the project, with
  the sha256 of the original and of the copy in this archive (see "Editing for publication" below).
- `MODES.txt`: the mode of every file other than `MODES.txt` and `SHA256SUMS`. Shell scripts are executable
  (mode 755); all other files have mode 644.
- `SHA256SUMS`: the sha256 of every other file, in all four parts. Check with `sha256sum -c SHA256SUMS` in this
  directory after unpacking all parts.

## Licences

The source code and scripts (files ending in `.c`, `.h`, `.py`, `.sh`, `.lean`, the other program files, and all files of `lean/`) are licensed
under the Apache License 2.0 (`LICENSE`). The data, logs, results and documentation are licensed under the Creative
Commons Attribution 4.0 International licence (CC BY 4.0, `LICENSE-DATA`). Two inputs come from published sources and should be cited as such: the 41 self-dual [36,18,8]
codes (`klein/codes36.txt`, `klein/impl2/data/36-d8.magma`) are generator matrices from the database of
Harada and Munemasa, and the inputs of the known-code check in `order3/classification/program1/known/` are
transcribed from the papers cited in "Tests of individual components". nauty is not included; it is available from its authors under its
own licence.

## Requirements

- A C compiler. We rebuilt the programs for this supplement with GCC 15.2.0 on x86-64 Linux; the order-5 search
  uses OpenMP.
- Python 3. Some scripts also need numpy, and two need python-flint (`klein/qrcheck/qrgen.py`,
  `order3/labelling/octad_growth/src/control48/qr48.py`).
- nauty 2.9.3 by B. D. McKay and A. Piperno (`nauty2_9_3.tar.gz`, sha256 9fc4edae04f88a0f5883985be3b39cf7f898fd6cc96e96b9ee25452743cc1b5b, from
  https://pallini.di.uniroma1.it/) for the order-3 programs, and nauty's `dreadnaut` for the automorphism groups of
  the 41 codes in `klein/`. `order3/classification/build_nauty.sh` builds the library that the order-3 programs link
  against.
- zlib for `order3/cross_check/src/cscan.c`.
- For `lean/`: elan, the Lean version manager (see "Lean formalization").

Version 1 includes no compiled binary; version 2 includes the 21 executables of the main runs of Theorem D
(`order2/engines/`). The sha256 of the binaries that produced the main results are recorded in the manifests named in
each section. A rebuild with another compiler or on another processor gives a different binary;
the re-tests below compare outputs, not binaries.

## Conventions in the records

- The records name the machines that ran the computations by labels. hostA and hostB ran the order-5 search, its
  independent implementation and its cross-checks. hostB also ran Implementation I and the third solver of Proposition 3.8, and
  the octad-growth program on the classes with index below 3 600 000. hostF and hostG ran the octad-growth program
  on the other classes, and hostC, hostD and hostE ran the point-placement program. The same label means the same
  machine throughout the archive.
- Home directories appear as `<HOME>` and account names as `<USER>`.
- In `order2/`, machines also appear as hostH to hostM and as fleet01 to fleet104 (the machines of the package
  fleet), and machine families as famA, famB and famC (processors with AVX-512, including VBMI and GFNI) and famD,
  famE and famF (AVX2 only); the number after a family label is the number of hardware threads. CPU models appear
  as `<CPU>` and cloud zones as `<ZONE>`.
- Some records and source comments use two working-directory labels: `c3class` (the first classification program and
  the octad-growth program) and `c3explore` (the second classification program and the point-placement program).
- In `order2/`, some records whose sha256 is cited in another record keep the names of further working directories:
  `c2explore` (exploration and the runs outside the fleet), `c2struct` (package builder), `c2alg` (search programs),
  `c2fleet` (package fleet), `auditc3` and `auditlwe` (the cross-checks) and `y39indep` (independent re-searches). In
  all other files of `order2/` these labels were replaced.
- Logs keep the CPU and wall-clock times of the original runs. A rerun reproduces node counts and results, not times.
- Large text files are stored gzip-compressed (suffix `.gz`; decompress with `gzip -dk`). Where the original was an
  uncompressed file, its bytes are those of the decompressed file.
- Splitting into parts: in a parallel run of the search of Proposition 3.8 (Implementation I) or of a search of
  Theorem D, the nodes at the split level are numbered in depth-first order, and part j of P expands
  the nodes whose number is congruent to j modulo P. Every part recomputes the levels above the split level, so each
  node at or below the split level is expanded by exactly one part. Node counts of split runs count each node once,
  including the levels that every part recomputes; the few records that add the counts of all parts
  instead are marked where they are described.
- Terms of the checks: an implementation is independent if it shares no code with the program it checks, and a
  cross-check is a re-examination of a reduction or a program in which the quantities reproduced are recomputed, with
  independently written code unless stated otherwise. Implementation II (Sec. 7) was written from a statement of
  the problem, and the independent implementation of Theorem A from the statement of Proposition 2.4. Planted
  solutions are known solutions inserted into an instance, and a removal certificate certifies that a child of a
  search node is removed.

## Theorem A: no automorphism of order 5 (directory `order5/`)

Theorem A rests on Proposition 2.4: there is no 7 x 7 matrix U over F16 with UU* = I such that M(a) + M(aU) >= 16
for every nonzero a. The search of Sec. 2.5 proves it. The search program builds U row by row in the normal form of Lemma 2.5.
It ran as 224 jobs (7 keys times 32 hash classes of the depth-1 row), with threshold 16 and 8 threads per job. Two machines shared the jobs: the one called hostA in file names ran the odd hash
classes and hostB the even ones. Every job finished and reported no solution. The job logs reproduce Table 1.

### Contents

| Path | Contents |
|---|---|
| `search/` | The search program and its tools in C (OpenMP). `gen4.c` is the main-run search program. `gen4d5.c` is the same program with a dump of every partial matrix with five rows. `gen2h.c` is the version without optimisations (no skip lists, no static filter at depth 1). `tester.c` is the brute-force tester, `planted2.c` the planted test, `ngcount.c` the count for Lemma 2.3. `selftest.c` writes the field and weight tables to `tables_c.txt`; `unit.c` prints 20 000 random packed vectors with their pattern index, Hermitian product and scalar multiple. `common.h` contains the tables shared by these programs. `run_generic.sh` starts all jobs of one hash parity; `run_d5.sh` with `parts5.txt` reruns the 56 jobs that have five-row nodes with `gen4d5`. `development/` keeps earlier versions; their comparison runs are in `logs/validation/hostB/`. |
| `reference/` | Python reference code: `f16.py` (the field F16, the map psi and the weights), `model.py` (explicit binary model of length 72), `c0check.py` (Lemma 2.1), `xcheck_tables.py` and `unitcheck.py` (the C tables and routines against the Python code), `f16check.py` (norm classes and their representatives 1, 1+t, 1+t^2). |
| `logs/main_run/hostA/`, `logs/main_run/hostB/` | The job logs `r<key>_p<class>.err`, the empty solution files `r<key>_p<class>.out` (a solution would appear there as a SOLUTION line), and the end markers `done_0`, `done_1`. `logs/main_run/collect.sh` aggregates the logs into Table 1. |
| `logs/validation/hostA/xchk/` | `gen2h` on five jobs, (0,11), (2,9), (4,5), (5,3) and (6,1). |
| `logs/validation/hostB/` | The tester at threshold 16 (`t16.err`, 100 comparisons) and 12 (`t12.err`, 36 comparisons), the planted test (`pl2.err`, 200 of 200 accepted), and short runs on small fractions of a job, made while the program was developed (`s*`, `e*`, `g2s*`, `gen2h.r*`, `gen3h.r*`; the last two name the program that wrote them). |
| `five_row_nodes/` | `d5/`: logs and dumps of the 56 jobs that have five-row nodes, rerun with `gen4d5`. `depth5_nodes.txt`: the 192 five-row nodes (one line `DEPTH5: r0 r1 r2 r3 r4` per node; rows in hexadecimal, nibble j = coordinate j of the B side; rows for the A-coordinates 0, 1, 3, 2, 4). `check6.py`: independently written check of the last level (Python, numpy). `check6_all.out`: its output on the 192 nodes. `indep_depth5.txt` and `check6_indep_depth5.out`: the eight five-row nodes of the independent implementation and the output of `check6.py` on them. |
| `independent_implementation/` | The independent implementation, with its own field arithmetic and its own normal form. `src/` (C and run scripts), `py/` (Python checks and `stats.py`, which tabulates the runs), `results/hostA/logs/`, `results/hostB/logs/` (all run logs: the complete search for each of the seven keys `full_k*`, sampled runs, planted tests, dumps and their checks), `results/local/` (unit tests of the field code). |
| `cross_check/` | The order-5 cross-check: its code and its outputs. `indep_patterns.py`, `cmp_mtab.py`, `sym72.py` (with `sym72.out`): pattern-level counts, the C tables, and the symmetries on explicit binary codes. `indep_check.c`: depth-1 recount for the seven keys (`reps_n1.txt` -> `n1_check.out`). `indep_check_parts.c`: the hash classes of the depth-1 rows (`rep<key>_indep_parts.txt` against `rep<key>_search_parts.txt`, `rep6_children.txt`). `indep_check2.c`, `indep_check3.c`: node re-checkers that enumerate the whole orthogonal complement. `gen4dump.c`, `gen4dump2.c`: `gen4.c` plus print statements, used to dump nodes of 13 rerun jobs. `runs/`: the run scripts `chain*.sh`, the reruns of the tester and the planted test (`t16.err`, `t14.err`, `t12.err`, `p12.err`), the dumps and logs of the 13 rerun jobs (`d_*`, `s_*`, `f_r6_p1.*`), the sampled node lists, and the checker outputs `chk_*.txt`. |

### Building and rerunning

`five_row_nodes/check6.py` and `independent_implementation/py/validate*.py` need numpy.

    sh order5/search/build.sh
    sh order5/cross_check/build.sh
    sh order5/independent_implementation/build.sh

`search/build.sh` uses `gcc -O3 -march=native -fopenmp`. With GCC 15.2.0, on the machine where the sources were
kept, this command reproduced the `gen4` binary stored there byte for byte. The main-run binaries were compiled on the two machines that ran them.

One main-run job, for key r and hash class p (THRESH defaults to 16):

    cd order5/search
    env OMP_NUM_THREADS=8 NPART=32 PART=p REP_ONLY=r ./gen4 > r<r>_p<p>.out 2> r<r>_p<p>.err

The jobs took between 85 s and 2 649 s each with 8 threads.
`WORKDIR=<dir with gen4> sh run_generic.sh <parity> 32 48 8` runs all jobs of one hash parity, as on the two
machines. `sh order5/logs/main_run/collect.sh` reads the job logs and prints the node counts of Table 1 per key and
in total, the number of complete jobs (224 of 224) and the number of solutions (0).

A short check of the build: with one thread,
`env OMP_NUM_THREADS=1 NPART=1000 PART=5 REP_ONLY=6 ./gen4` took 13 s and printed the node counts
`1 73 38557 329414 0 0 0`, the same as `logs/validation/hostB/e6.err`.

Other commands, each under a minute on one thread unless stated:
- `env THRESH=16 NDIVES=1 SEED=20261018 ./tester` repeats the first dive of `cross_check/runs/t16.err`.
- `env THRESH=12 NTESTS=2 SEED=5551212 ./planted2` repeats the first two tests of `cross_check/runs/p12.err`.
- `./ngcount` prints 0 (Lemma 2.3).
- `./selftest` rewrites `tables_c.txt`. Then, in `reference/`, `python3 xcheck_tables.py ../search/tables_c.txt`, and
  `python3 unitcheck.py <output of ../search/unit>`.
- `python3 c0check.py` and `python3 f16check.py` in `reference/`. (`model.py` builds a random maximal isotropic subspace
  by rejection sampling and runs much longer.)
- `python3 five_row_nodes/check6.py five_row_nodes/depth5_nodes.txt` re-checks the 192 five-row nodes; on one thread it took
  103 s, and its output was byte-identical to `check6_all.out`.
- In `independent_implementation/`: `mkdir -p logs; src/search 16 6 all` runs the complete search for its key 6 in under
  a second. Its node table equals `results/hostA/logs/full_k6_all.log`; the "fail stats" lines are diagnostic counters
  that are not thread-safe, so they vary with the number of threads. `src/items 16` reproduces
  `results/hostA/logs/items16.log`. `python3 py/stats.py` tabulates the shipped run logs.
- In `cross_check/`: `./indep_check < reps_n1.txt` reproduces `n1_check.out`. `env PARTOF=1 ./indep_check_parts` on the last
  line of `reps_n1.txt` reproduces `rep6_children.txt`. `./indep_check3 < runs/s_r6_p20.out` reproduces
  `runs/chk_s_r6_p20.txt`. `runs/chainD.sh` regenerates the dump of job (6,1)
  (`SMP1=1 SMP2=1 SMP3=1 NPART=32 PART=1 REP_ONLY=6 ./gen4dump2 > f_r6_p1.out`), and `runs/chainE.sh` repeats the
  complete recount (`./indep_check3 < f_r6_p1.out`); the recount took 25 minutes with 32 threads.

### Checks of Theorem A

The order-5 cross-check re-implements the field arithmetic, e8, M, GL(3,2), the normal form and the enumeration of
orthogonal complements; its code is in `cross_check/`. Several rows also use
the independent implementation in `independent_implementation/`.

| Check | Outcome | Files |
|---|---|---|
| Order-5 cross-check, depth 1: all depth-1 counts recomputed. | Equal to the counts of the main run. | `cross_check/indep_check_parts.c`; `cross_check/rep<key>_indep_parts.txt`, equal to `rep<key>_search_parts.txt` (the depth-1 counts of the job logs) |
| Order-5 cross-check, reruns: 13 jobs of the search rerun, one of them node by node (job (6,1), 13 254 989 nodes). | Counts equal to those of the main run; the node-by-node recount finds 0 disagreements and 0 invalid nodes. | `cross_check/gen4dump.c`, `gen4dump2.c`, `cross_check/runs/chainC.sh`, `chainD.sh`; logs `cross_check/runs/d_*.err` (8 jobs), `s_*.err` (4 jobs), `f_r6_p1.err`; recount `cross_check/indep_check3.c`, `cross_check/runs/chainE.sh`, `cross_check/runs/chk_f_r6_p1.txt` (the dump is left out; `chainD.sh` regenerates it) |
| Order-5 cross-check, nodes: 50 of the 192 five-row nodes re-checked, also without symmetry rules, and a sample of 7 849 nodes with 2 to 5 rows. | None of the 50 five-row nodes has a sixth row; no disagreement in the sample. | `cross_check/runs/chk_all_sampled_local.txt` (740 + 790 + 6 269 + 50 nodes, 0 disagreements); node lists `cross_check/runs/f_sample.txt`, `fs2.txt` to `fs4.txt`, `all_n5.txt`, `all_parents.txt`; the dumps `d_*.out`, `s_*.out` |
| Lemma 2.1 (Sec. 2.2): the mass formula 5 791 500 + 4 054 050 = 9 845 550 for the doubly-even self-dual codes of length 16, and the placements of the two fixed points compatible with the weight conditions, enumerated. | Mass formula confirmed; 64 valid placements in e8 + e8, all in different components; none in d16+. | `reference/c0check.py` |
| Lemma 2.3: exceptional isotropic vectors, searched for by the search program (all 2^28 vectors), by the order-5 cross-check (all 4^7 patterns) and by the independent implementation (all 2^28 vectors). | None found by any of the three. | `search/ngcount.c`; `cross_check/indep_patterns.py`; `independent_implementation/src/items.c` and `results/hostA/logs/items16.log`, line ITEM2 |
| abs(R) = 42 437 500, the seven keys with their orbit sizes and the depth-1 column of Table 1, recomputed by the order-5 cross-check (812 patterns) and by the independent implementation (also by brute force over all 2^28 vectors). | All values reproduced by both. | `cross_check/indep_patterns.py`, `cross_check/indep_check.c` with `reps_n1.txt` and `n1_check.out` (column indep_free: the depth-1 rows); `independent_implementation/results/hostA/logs/items16.log` (ITEM1: abs(R); the orbits; ITEM3: the depth-1 rows) |
| The independent implementation (Sec. 7), with its own normal form, searching for solutions: 130 857, 81 715 595, 1 248 185 306, 8 and 0 nodes with 2, 3, 4, 5 and 6 rows; its eight five-row nodes re-checked by independently written code (480 candidates). | No solution. | `independent_implementation/src/search.c`; `results/hostA/logs/full_k*_*.log`, `results/hostB/logs/full_k0_s1.log`; `py/stats.py` (prints these totals); `five_row_nodes/indep_depth5.txt`, `five_row_nodes/check6_indep_depth5.out` |
| A variant of the search program without two shortcuts (skipping words with M(a) >= 14 in the full test, and a filter at depth 1 that the normal form implies), run on part of the search (five jobs). | Node counts per depth equal to those of the main run. | `search/gen2h.c`; `logs/validation/hostA/xchk/*.err`, whose TOTAL lines equal those of the main-run logs of the same jobs |
| Last level: each of the 192 five-row nodes re-validated, and the 60 vectors of norm 1 in its orthogonal complement tested as sixth rows against every word, by independently written code. | All 11 520 candidates fail. | `five_row_nodes/depth5_nodes.txt`, `five_row_nodes/check6.py`, `five_row_nodes/check6_all.out` (last line: nodes 192, invalid 0, candidates 11520, valid sixth rows 0); the dumps in `five_row_nodes/d5/`, made with `search/gen4d5.c` and `search/run_d5.sh` |
| Parity: the transposition (2 4) of the coordinates of A preserves the traces of all lines on {0, 1, 2, 3, 4} and pairs the five-row nodes; the five-row nodes of each job counted. | An even count for each of the 224 jobs. | `logs/main_run/host*/r*_p*.err` (fifth number of the TOTAL line); `cross_check/runs/all_n5.txt` (the 50 re-checked five-row nodes form 25 pairs) |

### Which files support which statement

| Paper | Files |
|---|---|
| Sec. 2.1 and Lemma 2.5, norm classes with representatives 1, 1+t, 1+t^2 | `search/common.h`; `reference/f16check.py` |
| Sec. 2.5 and Table 1: abs(R), the keys, patterns and rows in R | header lines of the job logs |
| Table 1, columns k = 2 to 5, totals; Proposition 2.4 (no partial matrix with six rows) | `logs/main_run/host*/r*_p*.err` (line "rep ... nodes:"), aggregated by `logs/main_run/collect.sh`; empty `.out` files (no solution) |
| Sec. 2.5, the jobs and their running time | `search/run_generic.sh`; times in the job logs |

## Proposition 3.8: no subgroup C2 x C2 (directory `klein/`)

This directory contains the reduction data, the search program of Sec. 3.6 (Implementation I in file names and below), the two programs of Sec. 7 that check it (Implementation II, a second, independent implementation, and the guess-and-determine program, called the third solver), their inputs and outputs, the tests on known codes, and the code and outputs of the cross-checks. All Python scripts find their
inputs relative to their own location, so they can be run from any directory. Removal certificates are called
kill certificates in file names (`kill/`, `killall/`, `lwe_kill.c`, `verify_kills.py`).

### Contents

| Path | Contents |
|---|---|
| `codes36.txt` | The 41 self-dual [36,18,8] codes of (L3), as generator matrices from the database [HMdb] (see "Licences"). Codes are numbered 0 to 40 in file order. |
| `model/` | Reduction and instance generators. `autinv.py` computes Aut(Y) of each code with nauty (dreadnaut) and writes `invs.pkl`; `v4sat.py` implements the model of Sections 3.1-3.5 (forms, constraints, conjugacy classes of fixed-point-free involutions); `classes.py`, `centr.py`, `autcheck.py` list and check the classes; `lw_all_list.txt` lists the 119 instances (code, class). `lwprep.py` is the instance generator of Implementation I and `lwall.sh` runs it on all 119 instances; `v4export.py` is the instance generator of the third solver. `lwe.c` is the later version of Implementation I, which adds only an optional tree-size estimation mode (PROBE). Test scripts: `control48v4.py`, `exp48.py`, `lwtest48.py`, `lwtest48_all.py` (with the copy as run, `lwtest48_all.py.as_run`), `verify48.py`, `verify48_all.py`, `verify48_chunk.py`, `control72v4.py`, `lwtest72.py`, `codes.py` (generators of the length-48 quadratic residue code). Records: `lwtest48_all.log`, `verify48_all.log`, `sol48.txt`, `sol48_all.txt`, `v48chunk/`, `controls.txt`, `lwall.log`; `inst/qr48.txt` is the length-48 instance of the third solver. `totals.py` recomputes the run totals. |
| `impl1_runs/` | Implementation I as run. `lwe.c` is the source of the run binary (sha256 beginning 8c03fe18); `lwinst/` has the 119 instance files `lwf_*.txt.gz` and the generator logs `prep*_*.log` (N, gauge rank, level sizes); `lwrun.sh`, `lwrunall.sh`, `tasks.txt`, `tasks_all.txt` are the run drivers; `out/` (six instances x 64 jobs), `out35/` (instance 3_5, 64 jobs) and `outall/` (the other 112 instances, unsplit) hold the 560 job outputs. `MANIFEST_lwe.txt` records the sha256 of the generator, the run source, the run binary, the 119 instance files and the 560 outputs; `check_manifest.py` checks it. `lw_unique.py` computes the node totals; `totals.txt` is the totals record with its correction note; `lwsum.py`, `run.log`, `runall.log` are records of the runs. |
| `gd_runs/` | The third solver (guess-and-determine program) as run. Sources `v4gd3.c`, `v4gd3fix.c` (64-bit masks) and `v4gd4.c` (128-bit masks); `inst/v4_*.txt.gz`, the 119 instance files; `v4run.sh`, `v4rerun.sh`, `tasks.txt`, `rerun_tasks.txt`, `SWAP_TIME`, `wide_status.txt`, `run.log`, `rerun.log`; outputs `out/` (16 jobs for each instance other than 0_0), `out2/` (the 57 reruns described below) and `test/` (instance 0_0, 64 jobs). `v4status.py` and `gd_unique.py` select the outputs and compute the totals. |
| `impl2/` | Implementation II. Sources `search.c` (main-run build), `search_v1.c` (earlier build with the same search logic), the Python modules (`gf2.py`, `instance.py`, `order.py`, `export.py`, `autgroup.py`, `fpfclasses.py`, `structure.py`, `check41.py`, `ineq41.py`, `run_aut41.py`, `prep72.py`, `prep72b.py`, `prep_alt.py`, `check_gauge.py`, `final_table.py`, `summarize.py`), the tests on known codes (`control48.py`, `control80.py`, `control80b.py`, `test_small.py`, with logs, result files and the length-48 and length-80 instances), and the removal-certificate checker (`verify_kills.py`, `cert_driver.py`, `witness_driver.py`, `witness_slices.sh`, `reverify.py`). `data/` contains the 41 codes as read from the database (`36-d8.magma`, `codes41.json`) and the automorphism groups, involution classes and structure data computed from them. Instances: `inst2/` (main-run basis orders), `inst3/` (alternative orders for eight instances), `inst/` (the first-heuristic orders used for the second run of 111 instances), each as `.txt.gz` with a `.json` description. `results/`: `out/` (first phase: 119 single jobs with a 1200 s limit), `out2/` (the 320 split jobs of the five largest instances, main-run basis orders), `out3/` (the same five instances under alternative orders), `final_table.json`, `summary.json`, `table.txt`, `p1_summary.json`. `remote/`: the command lines of the main run's three phases (`p1.cmds`, `p2.cmds`, `p3.cmds`) and their runner `runq.sh`. `logs/`: the second run of 111 instances (`run_*.out`), the removal certificates (`cert_*.out`, `w*_i72_*.out`, `w3_*.json`, `wd_*.log`, `rv_*`), instance preparation logs. |
| `qrcheck/` | Minimum weights of the extended quadratic residue codes of lengths 48, 72, 80: `qrgen.py`, `qrmin.c`, the generator matrices `qr48.txt`, `qr72.txt`, `qr80.txt`, `RESULTS.txt` and `SHA256SUMS`. |
| `checks/impl1/` | Cross-check of Implementation I: programs in `scripts/` (independent GF(2) re-derivation of the instance files `indep_check.py`, end-to-end test against explicit codes `e2e.py` with the low-weight enumerator `lowwords.c`, the naive search program `naive.c`, the sub-instance tests `pin.py` and `diff_test.py`, removal witnesses `lwe_kill.c` and `witness.py`, the instrumented rerun `lwe_xcheck.c` and `compare_repro.py`, reachability `reach.py`, `methods.py`, `w10check.py`, the length-48 test `qr48_control.py`, run accounting `acct.py`) and their outputs: `chk/` (119 instance re-derivations), `e2e/`, `kill/`, `killall/`, `wit_box/`, `diff/`, `diff_box/`, `qr48/`, `reach/`, `repro/` (the complete rerun of the 560 jobs, `compare_final.txt`), `regen/` and the hash lists `local_inst_sha.txt`, `box_inst_sha.txt`, `box_regen_sha.txt`, `box_lwxcheck_inst_sha.txt`, `box_hashes.txt`. |
| `checks/gd/` | Cross-check of the third solver and of the reduction: programs in `scripts/` (automorphism groups and canonical forms `aut_xcheck.py`, `canon_check.py`; instance checks `e2e_check.py`, `e2e_exact.py`; brute force `brute.c` with `mkinst.py`, `mkinst2.py`, `run_planted.sh`, `run_pinned.sh`, `analyze_planted.py`, `check_pinned.py`; node accounting `acct.sh`; root propagation `rootprop.py`), the versions with run-time checks in `dbg/` (`v4gd3dbg.c`, `v4gd4dbg.c`, logs), and the outputs `aut_check.txt`, `e2e/`, `e2e_exact.log`, `planted_*.log`, `planted_summary.txt`, `pinned_*.log`, `pinned_summary.txt`, `acct/`, `acct_*.log`, `rerun/`, `wide_nosplit/`, `rootprop_all.log`, `bogus_list.txt`, `local_inst_md5.txt`, `box_inst_md5.txt`. |

### The search programs

At a node of level t, the children that a constraint word y removes are either none or a coset v_0 + ker L_y
(Sec. 3.6). Implementation I removes them from a bit vector of length 2^{k_t}, or, when
2^{k_t} <= abs(Bad(y)) (2^{dim ker L_y} + 4), runs through all children in Gray-code order instead. It starts the
basis w_0, ..., w_17 with a basis of the fixed space Y^beta and then completes it: each new basis vector maximises the
number of words of weight at most 14 in the span, and is itself of weight at most 14 when possible. Implementation II
always removes children from a bit vector; it chooses the first rows of the basis inside Y^beta or inside Y(1+beta)
by a greedy rule and keeps the schedule with the smallest estimated work.

### Building and rerunning

`model/autinv.py` and `impl2/run_aut41.py` need nauty's `dreadnaut` on the PATH. The build flags of the original runs
were not recorded; the commands below are the ones we used to re-test the shipped sources.

- Implementation I: `cd impl1_runs; gcc -O2 -o lwe lwe.c`. Usage `./lwe INSTANCE [SPLITLEVEL NPART PART]`; the seven
  largest instances were split at level 4 into 64 jobs (for example `./lwe lwinst/lwf_21_2.txt 4 64 P`, P = 0..63) and
  the other 112 ran as single jobs. Example: `gzip -dk lwinst/lwf_37_1.txt.gz;
  ./lwe lwinst/lwf_37_1.txt` reproduces the LEVEL lines of `outall/lw_37_1.out` in well under a second.
- Third solver: `cd gd_runs; gcc -O2 -o v4gd4 v4gd4.c -lm` (likewise `v4gd3fix.c`, `v4gd3.c`). Usage
  `./v4gd4 INSTANCE WMAX MODE HEUR SPLITDEPTH NPART PART LIMIT SEED`; the runs used
  `./v4gd4 inst/v4_X.txt 14 search 1 5 16 P 0 1` (P = 0..15), and split depth 6 with 64 parts for instance 0_0.
- Implementation II: `cd impl2; gcc -O3 -march=native -o search_v4 search.c -lm`. Usage
  `./search_v4 INSTANCE [NJOBS JOB SPLITLEVEL [MAXSOL]]`; the split runs used `./search_v4 inst2/i72_X.txt 64 J 9`.
  `remote/p1.cmds`, `p2.cmds` and `p3.cmds` are the exact command lines of the main run's three phases (run with
  `remote/runq.sh CMDFILE PARALLEL`); `run72.sh` ran the second run of 111 instances and `witness_slices.sh` the extra
  certificate sampling.
- Instance generation: `cd model; python3 autinv.py` (writes `invs.pkl`, about 10 s), then
  `python3 lwprep.py CODE CLASS lwinst/lwf_CODE_CLASS.txt fixedfirst` (about 4 minutes per instance; `lwall.sh` runs
  all 119) and `python3 v4export.py CODE` (writes `inst/v4_CODE_*.txt`). The regenerated files are byte-identical to
  the shipped ones (re-tested on instance 37_1 for both generators).
- Totals: `python3 impl1_runs/lw_unique.py impl1_runs`, `python3 gd_runs/gd_unique.py gd_runs`, `python3 model/totals.py`,
  `cd gd_runs; python3 v4status.py`.
- Manifest of Implementation I: `cd impl1_runs; python3 check_manifest.py` (682 entries agree; the generator line is
  reported as edited and the binary as not shipped, see "Provenance of the files and records").
- Quadratic residue codes: `cd qrcheck; python3 qrgen.py 47 qr48.txt; gcc -O2 -o qrmin qrmin.c; ./qrmin qr48.txt 5`
  (T = 5, 5, 7 for p = 47, 71, 79).
- Small tests: `cd impl2; python3 test_small.py` needs the binary `search` (built from `search.c` or `search_v1.c`)
  next to it and takes about 75 s. `model/lwtest48_all.py` needs a binary `lwe` in the working directory and numpy;
  it rebuilds all 64 codes and checks each on all 2^24 codewords; it did not finish within 5 minutes in the re-test for this supplement.
  `model/lwtest72.py 9 7 6 5` needs a binary `lwe` in the working directory and takes under a minute; it prints
  the solution counts of the test at length 72 among the component tests (`model/lwtest72.log`, regenerated on 2026-10-23).

### Checks of Proposition 3.8

Two cross-checks re-examine the programs of the main runs: the Implementation I cross-check (`checks/impl1/`) and the
third-solver cross-check (`checks/gd/`), which also recomputes parts of the reduction.

| Check | Outcome | Files |
|---|---|---|
| Implementation I cross-check, instances and removals: all 119 instances re-derived and regenerated; explicit words of weight 8 or 12 for every removal of six small instances (111 812) and for a sample of 274 483 removals (577 894 completions). | Instances identical to those searched; every checked removal justified by a word of weight 8 or 12. | `checks/impl1/` (`chk/`, `regen/`, `kill/`, `killall/`, `wit_box/`) |
| Implementation I cross-check, explicit codes and sub-instances: 2 800 codes built from random forms and from forms at the deepest levels reached by the search; the length-48 test; 17 832 sub-instance tests against an independent naive search program (2.67 x 10^8 nodes compared). | In the 2 800 codes, every violated constraint carries a word of weight less than 16 and every such word lies over a violated constraint; 64 solutions at length 48 in both programs; every compared node agrees with the naive search. | `checks/impl1/` (`e2e/`, `qr48/`, `diff_box/`) |
| Implementation I cross-check, rerun: the search rerun completely, and 312 295 260 of its nodes re-evaluated naively. | The rerun reproduces every per-level count and finds no solution; every re-evaluated node agrees with the naive evaluation. | `checks/impl1/repro/compare_final.txt` |
| Third-solver cross-check: solution sets against brute force on 30 sub-instances with planted solutions (501 solutions, with and without splitting the search: unsplit and split into 3 and 5 jobs); 7 tests on instances with N+1 in {65, 66} in which some variables are fixed to given values; node accounting for split searches on five instances; about 61 000 run-time invariant checks; unit propagation at the root recomputed. | Solution sets agree with brute force; exact node accounting; no invariant check fails. | `checks/gd/planted_summary.txt`, `planted_*.log`, `pinned_summary.txt`, `pinned_*.log`, `acct/`, `acct_*.log`, `dbg/`, `rootprop_all.log`, `wide_nosplit/`, `rerun/` |
| The 41 codes: self-duality, minimum weight 8 and pairwise inequivalence (canonical forms of the graph on the coordinates and the words of weights 8 and 10), checked by the third-solver cross-check; self-duality and minimum weight also by Implementation II. | All 41 self-dual with minimum weight 8, and pairwise inequivalent. | `codes36.txt`; `checks/gd/scripts/aut_xcheck.py`, `canon_check.py`, output `checks/gd/aut_check.txt`; `impl2/check41.py`, `impl2/data/codes41.json` |
| Aut(Y_k) by nauty with two graph encodings; in the third-solver cross-check, the generators checked to be automorphisms and the order of the group they generate compared with the order reported by nauty (independent parser). | For all 41 codes: the encodings agree, the generators are automorphisms, and the generated group has the reported order. | `model/autinv.py`, `checks/gd/aut_check.txt`, `impl2/run_aut41.py`, `impl2/data/aut41.json` |
| Conjugacy classes of fixed-point-free involutions, recomputed by the third-solver cross-check and by Implementation II. | 119 in total from both; one code (no. 17 in database order, index 16 here) has none. | `model/lw_all_list.txt` (the 119 instances); `model/classes.py`, `checks/gd/aut_check.txt`, `impl2/fpfclasses.py`, `impl2/data/fpf41.json` |
| dim G = 18 and N for each instance, by Implementations I and II. | Agreement, with N = 63, 64, 65 for 106, 9 and 4 instances. | `impl1_runs/lwinst/prep*_*.log` ("gauge rank 18", N), `impl2/results/final_table.json` |
| Implementation I on all 119 instances, 6.08 x 10^10 nodes in total (unique count 60 828 714 380). The seven largest instances have 9.79 to 10.08 x 10^9 nodes (five of them), 5.33 x 10^9 and 5.40 x 10^9 nodes; the last has 18 nodes in Implementation II and is refuted at the root by the unit propagation of the third solver (Implementation I does no propagation). All other instances have at most 3.59 x 10^8 nodes each. | No solution. | `impl1_runs/out/` (the split instances 25_2, 15_2, 3_6, 20_7, 23_2 and 21_2), `out35/` (the split instance 3_5), `outall/`; `impl1_runs/lw_unique.py`; `impl1_runs/totals.txt`; `impl1_runs/MANIFEST_lwe.txt` |
| Implementation II on all 119 instances, 4.78 x 10^10 nodes in total: five instances with 9.35 to 9.74 x 10^9 nodes each, split at level 9; the others at most 1.03 x 10^7 nodes each; deepest level reached 14 of 18. A second run with a different basis order for every instance: 9.66 to 10.05 x 10^9 nodes for the five largest instances. | Neither run finds a solution. | `impl2/results/final_table.json`, `summary.json`, `table.txt`, `out/`, `out2/`, `out3/`; `impl2/logs/run_*.out`; `impl2/inst/`, `inst2/`, `inst3/` |
| Third solver on the 113 instances other than the six with the largest trees in Implementation II, 2.37 x 10^8 nodes in total (unique count 237 368 333); runs split at depth 5 into 16 jobs, and one instance at depth 6 into 64 jobs. | No solution. | `gd_runs/out/`, `out2/`, `test/`; `gd_runs/gd_unique.py`, `v4status.py`; `model/totals.py`; `impl1_runs/totals.txt` |
| Removal certificates for Implementation II: for a removed child, an independent checker exhibits a word of weight less than 16 and checks that it lies in the code for three completions of the remaining variables; all removals of 35 instances (132 834 removals, equal to the counts of the search), and a sample of 23 501 removals over all 119 instances, with words y of weights 8, 10 and 12. | Every certificate valid. | `impl2/verify_kills.py`, `cert_driver.py`, `witness_driver.py`, `witness_slices.sh`; `impl2/logs/cert_*.out`, `w*_i72_*.out`, `w3_*.json`, `wd_*.log`; field witness_verified in `final_table.json` |
| Coverage of the split searches of Implementation II for its five largest instances (320 jobs, 64 for each). | Every part ran to completion; the level-9 nodes expanded by the parts sum to 65 536 for each instance. | `impl2/results/out2/`, `out3/`, `summary.json` |

### Which files support which statement

| Paper | Files |
|---|---|
| Sec. 3.3, 3.5: r = 9, 8, 7; 5 932 to 6 328 constraint words; dim A in {81, 82, 83} | `impl2/results/final_table.json` (fields nparam, rank1b, ncons); `impl2/logs/prep_*.log` |
| Sec. 3.6: the search, Implementation I (its implementation is described under "The search programs") | `impl1_runs/lwe.c`, `model/lwprep.py` |
| Sec. 7: Implementation II | `impl2/search.c`, `impl2/order.py`, `impl2/instance.py` |
| Sec. 7: third solver (17-dimensional gauge, propagation, leaf check) | `model/v4sat.py`, `model/v4export.py`, `gd_runs/v4gd4.c` (and `v4gd3fix.c`) |

### Notes on the records

- The third solver was first run with a 64-bit build at the path `./v4gd3`, which was replaced by the 128-bit build
  (`v4gd4.c`) at the time recorded in `gd_runs/SWAP_TIME`. For the 13 instances with 65 or 66
  free bits, the 57 outputs written by the 64-bit build before that time are invalid (they report one node); they
  are listed as OLD in `wide_status.txt` (and in `checks/gd/bogus_list.txt`) and were rerun with the 128-bit build
  into `out2/`. The counting scripts use `out2/` for these 57 jobs and `out/` for all others; the superseded
  outputs stay in `out/` as records. For instances with at most 64 free bits the two builds differ only in the mask
  width.
- The node totals in the first part of `impl1_runs/totals.txt` add the job counts of split runs; its correction note
  gives the unique counts that the paper prints.
  The correction note refers to a report of the cross-check of Implementation I; the report is not included, and
  the results of that cross-check are the files in `checks/impl1/`.
- `impl1_runs/lwinst/prep_*.log` (seven files) belong to an earlier basis order of seven instances; they are kept
  because they also record the gauge rank and N. The instance files of that order are not included.

## Theorem C and the order-3 cross-check (directories `order3/classification/` and `order3/cross_check/`)

These two directories hold the classification of the Hermitian self-dual [24,12,8] codes over F4 (Theorem C),
the list of the 13 485 816 classes that the labelling tests of Theorem B read, the two classification
programs, and the cross-check of the order-3 computations ("Checks of Theorem C"). The labelling programs and their main-run results are in order3/labelling/.

### Contents

| Path | Contents |
|---|---|
| classification/class_list/ | The class list cls24.txt.gz, the histograms of Table 2, and a checker for the list. |
| classification/program1/ | The first classification program: sources (src/), its E_B classes (eb/), the count-only run and the length-16 and length-22 tests (cls/), random samples (samp/), and the known-code check (known/). |
| classification/program2/ | The second classification program: sources (src/, and f4code.h, the same file as the point-placement program's), a copy of the first program's canonical form used only to compare the two lists (c3c/), its E_B classes (n24/), the length-16 and length-22 tests (controls/), and the summary of its run over all 45 775 codes E_B (full/). |
| classification/build_nauty.sh | Builds the nauty library that all programs here link against. |
| cross_check/ | Code and outputs of the order-3 cross-check. |

### The class list (Theorem C, Table 2)

class_list/cls24.txt.gz has one line per class of codes up to monomial equivalence and conjugation,
13 485 816 lines, sorted by the first field. Each line has five fields, `KEY AUT A8 SC IDX`:
- KEY: 192 hexadecimal digits, 12 rows of 16 digits. Row r is "%08x%08x" of two 32-bit planes (a, b), and
  coordinate j (bit j, j = 0..23) of the row is the element a_j + b_j w of F4, where w^2 = w + 1 and the conjugate
  of w is w^2. The 12 rows are the reduced row echelon generator matrix of the canonical representative (the code
  relabelled by its nauty canonical labelling, program1/src/cform.h). KEY is the smaller of the canonical forms of
  C and of its conjugate.
- AUT: the order of the monomial automorphism group of C, including the 3 scalar matrices.
- A8: the number of words of weight 8 (A8 = 9 beta).
- SC: 1 if C is monomially equivalent to its conjugate, else 0; a line with SC = 0 stands for two classes up to
  monomial equivalence.
- IDX: the line of program1/eb/n24.L5.txt (counted from 0) with the code E_B that the class was glued from.

The decompressed list has sha256 58137da319c7447f8cd8da077c55b46184c2c1e4258709a0708af786a5ba805e.
`python3 class_list/check_class_list.py class_list/cls24.txt.gz` reads the list once, checks the format of every
line, and prints this sha256, the number of lines (13 485 816), the number of classes up to monomial equivalence
(26 924 931), the number of self-conjugate lines (46 701), and the histograms of beta and of AUT. Its output must
equal class_list/check_class_list.expected.txt; the two histograms are those of class_list/beta_hist.txt and
class_list/aut_hist.txt, which give the two columns of Table 2. The checker was written for this supplement.

### First classification program (program1/)

The program follows Sec. 5. Stage (i), src/ebclass.c, classifies the Hermitian self-orthogonal [16,k,>=8]
codes E_B for k = 2, ..., 5 by adding one vector per orbit; the results are program1/eb/n24.L2.txt to n24.L5.txt
(30, 393, 9 519 and 45 775 classes; n24s*.L4.txt are the slices of level 4 before merging). Stage (ii),
src/frames.c, enumerates the isometries (frames) for each E_B, keeps one code per class by the acceptance rule of
Sec. 5, and writes one line per accepted code; the merged and deduplicated output is the class list. The
canonical form is src/cform.h (nauty). src/run_L5.sh and src/run_F24.sh are the launch scripts of the two
large steps (240 and 288 slices).

Checks that this directory supports:
- Exact level counts (step (4) of the proof of Theorem C for this program): src/ebext.c writes the extension
  counts eb/n24.ext1.txt to n24.ext4.txt, and `python3 src/levelcheck.py eb/n24 5` prints EQUAL for every level.
- Double count (step (5)): the count-only run of frames.c (environment variable COUNTONLY=1, 16 slices) wrote
  cls/c24count.*.txt (canonical frames per E_B) and cls/c24count.*.log; cls/lhs_by_aut.txt and cls/rhs_by_aut.txt
  hold the two sides of the identity grouped by group order.
- Mass and membership (component tests): src/rsd.c samples uniformly random Hermitian self-dual codes; samp/ contains the
  samples of minimum distance 8 at lengths 22 and 24 with their logs; src/memb.c locates sampled codes in the list
  by class key; src/tisample.c and src/timiss.c are the corresponding checks for the E_B levels.
- Canonical forms (component tests): src/cftest.c and src/cftest2.c (random monomial images give identical keys).
- Tests at lengths 16 and 22 (component tests): cls/n16i.out (4 classes) and cls/n22d.*.out with cls/n22d.*.log (the 12
  slices of the length-22 run: 422 classes up to conjugation, 723 up to monomial equivalence);
  cls/n22count.txt is the count-only run at length 22; src/clsmiss.c locates the 898 sampled length-22 codes
  (samp/s22_all.txt); src/summarize.py prints class counts, mass and group orders of a set of output files.
- Known codes (component tests): known/kc.c builds codes from published data (input files known/in_*.txt; in_h24.txt is the
  machine input for the codes of [Har24], in_harada24_table2.txt the transcription it was made from) and prints
  key, AUT, A8, SC and the minimum distance; known/fam.c enumerates the double circulant and modified four-circulant
  families (outputs known/fam_*.txt); known/lookup.sh finds the keys in the list (outputs known/look_*.txt; it reads
  the decompressed list, so run `gunzip -k class_list/cls24.txt.gz` first or set CLS). known/out_a_d.txt and
  known/out_ah23.txt are the kc outputs.
- src/rank8.c prints the rank of the weight-8 words for lines of the list (this gives the two classes whose
  words of weight 8 span 11 dimensions, Sec. 7).

### Second classification program (program2/)

The second program (Sec. 7) was written independently of the first; it shares only the nauty library and, for the final
comparison, a copy of the first program's canonical form (c3c/, with c3c/SHA256SUMS). src/ebcls2.c classifies the
codes E_B level by level with its own canonical form (src/mycanon.h); n24/L1.txt to L5.txt are its levels,
n24/log*_*.txt the logs of the sliced runs, and n24/*.cfkeys.* and n24/*.kas the key sets and multisets used to
compare levels 4 and 5 with the first program. src/rglue.c enumerates the isometries orderly under S8 x F4^*,
with its own acceptance rule and canonical form (src/mycanon2.h), and records for each E_B the number of orbits
and the exact count N(E_B); src/ckey.c computes the first program's key of every accepted code.
src/rg_run_local_noclobber.sh and src/rg_run_remote_mkdir.sh are the worker pools of the full run (they differ only in
the lock method), and full/chain_local*.sh started further local pools.

full/all.eb contains one line per E_B (45 775 lines: id, |Aut|, self-conjugacy, orbits, N(E_B), accepted, distinct,
nodes, seconds) and full/E_B_L5.txt the E_B list it was run on. src/compare_full.sh compared the accepted codes
with the class list; its report is full/compare_report.txt, which gives the sha256 of both sorted extracts,
1370e6023a7dc3ee2320e248151c3fbcbfbc8604991c7e0c631fb1cffc332258, and the two sides of the double count. The extract of the class list can be recomputed from this supplement:
`zcat class_list/cls24.txt.gz | awk '{print $1, $2, $3, $4}' | sha256sum` prints 1370e602...2258 (the list is
already in sorted order). full/frozen_SHA256SUMS.txt is the checksum list of the program's sources, static
executables and results as they were run; full/nauty_SHA256SUMS lists the nauty files it was built against.

controls/n16, controls/n16b and controls/t16 are the length-16 test (4 classes, key set equal to the first
program's), controls/t22 the length-22 test.

### Cross-check (cross_check/)

This directory contains the code written for the order-3 cross-check and its outputs. It reads the class list and
the outputs of the two classification programs and of the two labelling programs; it shares no code with them,
except that rev_class/src includes the first program's frames.c to test its acceptance rule, rev_reclass includes
the second program's canonical forms, and gth/ holds copies of the octad-growth program's headers (gth/gtestS_xcheck.c is the harness built from them).

| Path | Check of Theorem B or C, or component test, that it supports |
|---|---|
| src/cscan.c, scan/full_[0-5].hist, .exc, .log | Steps (1)-(3): the scan of every line of the list (self-orthogonality, rank 12, no word of weight below 8, the listed A8), the two-round colour-refinement invariant of the supports of weight 8 (collisions in scan/inv_collisions.txt), and the group orders that it certifies directly. |
| src/autnd.c, scan/nd_all.txt, scan/nd_part_0*.aut | Step (3): the other group orders, computed with nauty. |
| src/ebext.c, src/autsmall.c, ebchk/, src/chain.py | Step (4): extension counts and automorphism groups computed independently; ebchk/L4full.aut and L5full.aut give the independently computed groups and keys of the levels 4 and 5. |
| rev_reclass/masschain.py, rev_reclass/m_L*.txt | Step (4) by a second independent implementation. |
| rev_reclass/ebinv.c, rev_reclass/ebinv.out | Invariance of the second program's keys of the codes E_B (4 578 tests, 0 failures). |
| src/cmp_count.py | The counts N(E_B) of the two programs, compared. |
| rev_reclass/gcount.c, rev_reclass/gc_*.out | The plain count on 13 codes E_B. |
| src/lhs.py, rev_reclass/dcount.py, rev_reclass/grp.txt | Step (5): both sides of the double count. |
| src/sampler.c, scan/samp_*.out, scan/found2000*, src/memb_map.py | Mass and membership with the sampler written for the cross-check (scan/samp_*.out: 3 000 000 samples each). |
| rev_reclass/cinv.c and cinv_*.out; rev_class/src/accinv.c and rev_class outputs | Invariance of key, |Aut_Mon| and self-conjugacy; the acceptance rule of the first program. |
| rev_class/src/dcirc.c, bdcirc.c, ebmemb.c | Double circulant codes and E_B membership. |
| src/red72.c, red/red20.out | The reduction checked on explicit codes of length 72. |
| src/sextet_gt.c, src/randinst.c, src/lab.c, labt/ | Three solvers: sextet instances against an independent enumeration, planted labellings in real codes and random families (labt/*.f8, *.f12 are the instance bitmaps). |
| samp/ | Runs of the point-placement solver written for the cross-check of the order-3 computations (src/lab.c) on 5 711 distinct classes, the union of all 3 862 classes with 9 <= |Aut_Mon| < 3|M24| (aut9.txt), all 225 with beta >= 94 (hibeta.txt, which contains G24 (x) F4; 79 of them are also in aut9.txt), 1 560 random classes (idx120.txt, idx240.txt, idx1200.txt) and 150 classes with |Aut_Mon| = 6, 9 or 12 (sym150.txt; 7 of them are also in aut9.txt). The runs are a9_*, hb_*, r120_*, r240_*, r1200_*, s150_*, sp_g24.*, sp_hi.* and sp_rest.*. |
| symt/ | Symmetry reduction with planted orbits on codes with |Aut_Mon| between 6 and 1 728 (symt/symtest.out). |
| gth/, rev_gtestS/ | Review of the octad-growth program: harness, the rank-11 classes (symchk_rank11.txt, rank11_nosym.txt), sextet instances against the enumeration (zchk*). |
| prov/, rev_csp5p/ | Review of the point-placement program: provenance of the main-run source (prov/csp5p.c is byte-identical to that source), instrumented builds, planted tests, a format scan of the per-machine input files. |
| src/cov_csp.py, cov/csp_cov_final.txt, cov/csp_status_final.txt, cov/samp_nodes*.txt | Coverage of the point-placement main run, second checker. |
| src/cov_gt.py, cov/gt_cov_final.txt, cov/hostBrun1/, cov/gtfinal/, cov/gtp/ | Coverage of the octad-growth main run, second checker (copies of the per-slice result files it read). |
| boxtest/ | Self-test kit for the main-run executables, with expected outputs. |
| rev_lit/scripts/lhs_check.py | Recomputes the left side of the double count, the mass and the histograms from the list. |

### Checks of Theorem C

Most checks of the classification were made by the order-3 cross-check, whose code and outputs are in `cross_check/`
(listed under "Cross-check (cross_check/)" above); the checks of the labelling programs are in "Checks of Theorem B".
Paths in this table are relative to `order3/`.

| Check | Outcome | Files |
|---|---|---|
| Stage (i), run by both programs: 30, 393, 9 519 and 45 775 classes of dimension 2, 3, 4 and 5; class keys compared at dimensions 4 and 5, and at dimension 5 also the multisets of (key, abs(Aut_Mon), self-conjugacy). | Agreement in all these comparisons. | `classification/program1/eb/n24.L2.txt` to `n24.L5.txt`; `classification/program2/n24/L2.txt` to `L5.txt`, with the key sets and multisets `n24/*.cfkeys.*` and `n24/*.kas` |
| Isometry search: the first program visits 5.74 x 10^9 leaves, of which 2.87 x 10^9 are canonical, and accepts 1.60 x 10^7 codes; the second finds 2.872 x 10^9 orbits of isometries, 3.474 x 10^14 isometries in total, and accepts 18 738 263 codes. | 13 485 816 classes from each, with identical multisets of (key, abs(Aut_Mon), A8, self-conjugacy). | `classification/class_list/cls24.txt.gz`; `classification/program2/full/all.eb`, `classification/program2/full/compare_report.txt` |
| Step (1) of the proof of Theorem C: every listed code checked for self-orthogonality, rank 12, no nonzero word of weight less than 8, and the listed A8 (order-3 cross-check). | All 13 485 816 pass. | `cross_check/src/cscan.c`, `cross_check/scan/full_[0-5].hist`, `.exc`, `.log` |
| Step (2): the support invariant of every listed code (order-3 cross-check). | 13 485 816 distinct values. | `cross_check/src/cscan.c`; `cross_check/scan/inv_collisions.txt` (empty) |
| Step (3): the automorphism groups and self-conjugacy flags, recomputed (order-3 cross-check). | 13 372 811 groups certified directly and 113 005 by nauty, all agreeing with the list. | `cross_check/src/cscan.c`; `cross_check/src/autnd.c`, `scan/nd_all.txt`, `scan/nd_part_0*.aut` |
| Step (4): independently computed extension counts and automorphism groups, a second independent implementation, and independent canonical keys of the classes of dimension 4 and 5 (order-3 cross-check). | The identity holds exactly for k = 0, ..., 4 (for k = 0, ext(0) = 713 843 361; for k = 4 both sides equal 23 376 798 468 859/2 903 040); the keys are distinct. | `cross_check/src/ebext.c`, `src/autsmall.c`, `ebchk/`, `src/chain.py`; `cross_check/rev_reclass/masschain.py`, `m_L*.txt`; for the first program, `classification/program1/src/ebext.c` and `src/levelcheck.py` |
| The counts N(E_B) of the two programs for all 45 775 codes E_B: the first program counts orbits of S8 x F4^*, which acts faithfully on 1^perp/<1> and so freely on the isometries, and its count is 120 960 times the number of orbits; a third, plain count on 13 codes E_B, four of them with N(E_B) = 0. | Equal for all 45 775, with the same abs(Aut_Mon(E_B)) and self-conjugacy; the plain count agrees on the 13. | `cross_check/src/cmp_count.py`; `cross_check/rev_reclass/gcount.c`, `gc_*.out` |
| Step (5), evaluated in rational arithmetic: the left side from the list, with the recomputed values of A8 and abs(Aut_Mon) (order-3 cross-check), and the right side from the counts of each program. | All values equal 526 493 209 678 523/322 560. | `cross_check/src/lhs.py`, `cross_check/rev_reclass/dcount.py`, `grp.txt`, `cross_check/rev_lit/scripts/lhs_check.py`; for the first program, `classification/program1/cls/lhs_by_aut.txt` and `rhs_by_aut.txt` |

### Building and rerunning

All programs are C99 with gcc and link against nauty 2.9.3 (see "Requirements"), and cscan also against zlib.
From order3/classification:

    ./build_nauty.sh /path/to/nauty2_9_3.tar.gz nauty     # configure + 7 library files, libnauty64.a
    export NAUTY=$PWD/nauty/nauty2_9_3
    program1/build.sh; program2/build.sh; ../cross_check/build.sh    # binaries in each bin/

Small reruns, each under a minute on one core, with the expected outcome:

    cd program1; mkdir -p out
    bin/ebclass 16 2 8 - out/n24 && cmp out/n24.L2.txt eb/n24.L2.txt           # 30 classes, identical
    bin/ebclass 10 2 6 - out/n16 && bin/ebclass 10 3 6 out/n16.L2.txt out/n16
    bin/frames 16 6 out/n16.L3.txt out/n16.out && python3 src/summarize.py 16 6 out/n16.out   # 4 classes, |Aut| 144, 360, 1008, 2880
    python3 src/levelcheck.py eb/n24 5                                          # ALL EQUAL
    bin/ebext 16 8 eb/n24.L2.txt | cmp - eb/n24.ext2.txt
    bin/clsmiss 22 8 samp/s22_all.txt cls/n22d.*.out                            # tested 898 missing 0
    python3 src/summarize.py 22 8 cls/n22d.*.out                                # 422 and 723 classes
    bin/kc < known/in_h24.txt                                                   # same lines as known/out_a_d.txt
    cd ../program2; mkdir -p out
    bin/ebcls2 16 8 8 1 out/L1.txt && bin/ebcls2 16 8 8 2 out/L1.txt out/L2raw.txt
    sort -u out/L2raw.txt | cmp - n24/L2.txt                                    # 30 classes, identical
    bin/rglue 10 6 controls/n16/L3.txt out/out16.txt && cmp out/out16.txt controls/t16/out.txt
    cd ../../cross_check/src
    python3 chain.py; python3 lhs.py; python3 cmp_count.py                     # exact equalities; 45775 of 45775 match
    cd ../rev_reclass; python3 dcount.py; python3 masschain.py
    cd ..; mkdir -p out; bin/cscan scan/head3000.txt 1 0 out/th && cmp out/th.hist scan/t_head.hist
    bin/red72 scan/head3000.txt 5 1                                             # RESULT OK

The Python scripts in cross_check expect to be run from their own directory. The full runs are
program1/src/run_L5.sh (level 5 of stage (i), 240 slices), program1/src/run_F24.sh (stage (ii), 288 slices;
the outputs are then deduplicated by key into the list), and for the second program rglue over all 45 775 lines
of full/E_B_L5.txt followed by src/compare_full.sh (the per-E_B times in full/all.eb add up to 252 087 seconds).

## Theorem B: no automorphism of order 3 (directory `order3/labelling/`)

Theorem B (Sec. 4) reduces to the following statement: for none of the 13 485 816 classes of Hermitian self-dual
[24,12,8] codes E in the class list (order3/classification/), a labelled Golay code on the 24 coordinates of E
satisfies the conditions (W8), (W10) and (W12) of Lemma 4.2. Two independently written programs, which share no source
file, decide this for a given code E. The point-placement program (`csp5p`, directory `point_placement/`, Sec. 4.3)
places the images of the points of a reference Golay code in the normal form of Lemma 4.4; the proof of Theorem B uses
its main run (Sec. 4.4). The point-placement program shares only the F4 arithmetic (`f4code.h`) with the second
classification program. The octad-growth program (`gtestS`, directory `octad_growth/`, Sec. 7) adds octads, tetrads and
sets of disjoint octads one step at a time. It includes `f4.h`, `f4code.h` and `golay.h` of the first classification
program, and with `sd_lowwords` from that `f4code.h` it finds the supports of the words of weight 8, 10 and 12 of E,
from which it builds the forbidden sets; its length-48 test also uses `cform.h` of that program. Both programs ran on
every class of the list and found no valid Golay code.

### Contents

| Directory | Contents |
|---|---|
| `point_placement/src/` | `csp5p.c` and `f4code.h` (the sources of the point-placement program), `octdod.txt` (the 759 octads and 2 576 dodecads of the reference Golay code), `g16_e8e8.txt` and `g16_d16p.txt` (doubly-even [16,8,4] codes for the length-48 test), `SHA256SUMS` |
| `point_placement/` | `README.md` (short description), `FORMATS.md` (input layouts, invocation, output line) |
| `point_placement/main_run/` | the driver `run_list.sh` and `summarize_run.py` with their checksums (`kit_SHA256SUMS`); `RUNPLAN.md` and `LEDGER.tsv` (division of the list into parts and their assignment to the three machines, with the partition argument); `strict_check.py` and its output per machine (`strict_host*.txt`); `inputsha_host*.txt` and `cls24sha_host*.txt` (hash of each machine's inputs and of the list lines in its ranges); `aggregate.py`; `COVERAGE_PROOF.txt`; `FINAL_MANIFEST.txt` and `FINAL_MANIFEST_v2.txt` (sha256 of all final files); `shares/` (sha256 of the parts of the list, compressed and decompressed) |
| `point_placement/main_run/results/` | the per-class main-run results: `hostD.out.tgz`, `hostE.out.tgz`, `hostC.out.tgz` (one `.out` file with one line per class, and one empty `.err` file, per part of 200 classes), `members_host*.sha256` (sha256 of every member), `aggregate_final.txt`, and `boxlogs/` (driver logs, file listings and the checksums of the programs on each machine) |
| `point_placement/planted_control/` | planted test run, made after the main run with the same executable on the same three machines: inputs (`p_*.bin` planted, `u_*.bin` unplanted forbidden-set bitmaps of three real classes), `code_*.txt`, `csp5p_plantdump.c` (the source with an added dump option that wrote the bitmaps), `run_control.sh`, `EXPECTED.txt`, `local_precheck_results.txt`, the results of the three machines (`box_results/`) |
| `point_placement/cross_checks/` | runs of both labelling programs on common instances: inputs (`inputs/`, `len16/`), outputs (`results/<set>/ch_NNN.csp` from csp5p, `.gt4` and `.gt9` from two earlier versions of the octad-growth program), the launch scripts, the comparison scripts `compare2.py` and `compare_pz2.py` (and their first versions `compare.py`, `compare_pz.py`), the sextet instances and their counts (`z_*`, `zc_*`), the sources gtest4 and gtest9 as compared (`gt4src/`, `gt9src/`), `dcirc.c` (double-circulant codes), `raw2compact.c`, `toB.py`, `gtest4_reported` |
| `point_placement/verify/` | `verify_c.c` and `verify_sat.sh`: builds the length-72 code from a solution and computes its full weight distribution in parallel parts (never needed, since no solution was found); a test run of the builder in 16 parts (`run_3976979/`; the code tested there has minimum weight 12) |
| `octad_growth/src/` | `gtestS_prod.c` (the source of the main-run executable) with `gcore.h`, `golay.h`, `f4.h`, `f4code.h`; `gtestS.c` (the same source with a check of the weight-8 span, which switches the symmetry reduction off when the span is deficient, the planting mode Q and an END option; the re-test of the two rank-11 classes in `octad_growth/rank11/` used a build with the span check, and the Q-mode runs a build with the planting mode); `gtest4.c` and `gtest9.c` (earlier versions used in the cross-checks); `gbfs.c` (reference enumeration of the 995 328 Golay codes containing a fixed sextet); `mkg24.c` (writes G24 (x) F4); `cform.h` (canonical form, used by `control48/chk.c`); `val/symchk.c`; `control48/` (length-48 test: `qr48.py`, `chk.c`, `lab16.c`, `codes16.txt`, `qr48_DE.txt`) |
| `octad_growth/main_run/` | `run_T24x.sh` and `stopper.sh` (launch and stop rule of the slices), `covcheck.py` and `covmanifest.py` (the two coverage checks), `COVERAGE.txt`, `MANIFEST.txt` (with the sha256 of every result file), `MANIFEST.txt.sha256`, `PROVENANCE.txt` (which executable wrote which result lines) |
| `octad_growth/main_run/results/` | the per-slice main-run results: `hostB/res0.txt` ... `res299.txt` and `stopper.log` (classes with index below 3 600 000), `x/res0.txt` ... `res739.txt` (the other classes) |
| `octad_growth/validation/` | Q-mode runs (`q_*.txt`), the rank-11 re-test with the main-run executable (`rank11.txt`, `rank11_prod_nosym.out`), `symchk.out`, G24 (x) F4 with the symmetry reduction (`g24f4.txt`, `g24f4s.out`), the sextet instances as forbidden-set bitmaps (`z_1` ... `z_7`), `z6.txt`, `planted_v3.txt`, `three.txt`, `cmpS.txt`, `cmpT.txt` |
| `octad_growth/rank11/` | the two rank-11 classes re-tested with the corrected program (`rank11.txt`, `rank11_gtestS.out`, `one1.txt`, `one2.txt`) |
| `self_tests/` | self-tests of both programs' main-run executables on all six machines, during the runs and afterwards: `README.txt`, input `boxtest_in.txt` (the first three classes of the list), expected outputs `exp_*.txt`, scripts `box_*.sh`, `norm.sh` (removes timing fields), raw and normalised outputs per machine (`res_host*.txt`, `n_host*.txt`), summaries `SUMMARY_mid.txt` and `SUMMARY_final.txt` |
| `process_checks/` | environment checks of every running main-run process (no diagnostic switch set): `envcheck_20261021T0015Z.txt`, `envcheck_20261021T1125Z.txt` and the scripts `envcheck.sh`, `envcheck2.sh` |

### Building

The point-placement program needs only a C compiler and libc:

    gcc -O3 -march=native -o csp5p point_placement/src/csp5p.c

The octad-growth program needs nauty 2.9.3 (see "Requirements"), built as a static library with 64-bit words:

    tar xzf nauty2_9_3.tar.gz && cd nauty2_9_3 && ./configure
    for f in nauty nautil naugraph schreier naurng nausparse nautinv; do gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -c $f.c; done
    ar rcs libnauty64.a nauty.o nautil.o naugraph.o schreier.o naurng.o nausparse.o nautinv.o

With `N` the nauty directory, in `octad_growth/src/`:

    gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -I$N -o gtestS gtestS_prod.c $N/libnauty64.a -lm   # main run
    gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -I$N -o gtestS_fix gtestS.c $N/libnauty64.a -lm   # corrected version
    gcc -O3 -march=native -o gtest4 gtest4.c;  gcc -O3 -march=native -o gtest9 gtest9.c
    gcc -O3 -march=native -o gbfs gbfs.c;      gcc -O3 -march=native -o mkg24 mkg24.c
    (cd val && gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -I$N -o symchk symchk.c $N/libnauty64.a -lm)
    (cd control48 && gcc -O3 -march=native -DWORDSIZE=64 -DMAXN=0 -I$N -o chk chk.c $N/libnauty64.a -lm && gcc -O3 -march=native -o lab16 lab16.c)

`covmanifest.py` needs numpy. `chk` reads `codes16.txt` and `qr48.py` writes `qr48_DE.txt` in the current directory.

The main-run executables were built with GCC 14.2.0 and `-march=native` on the machines that ran them:
the point-placement executable `csp5p_static_v3` (sha256 1f6222c7c7256a3ff641504b5281715bbb30f807a7c8408f35aacb83951b5141,
a static build of `point_placement/src/csp5p.c`) and the octad-growth executable (sha256
97be159fb07f010f7f81226bc986cb61f729b36f71f1f719c0e42b9905cd6564). The second was rebuilt bit for bit from
`gtestS_prod.c` on its machine with the command above (`PROVENANCE.txt`). The executables are not included.

### Small reruns (each well under a minute on one core)

    norm() { sed -E 's/ (wall|cpu|prep|t|tV3|tFP|tAT|tEXT)=[0-9.]+s?//g' "$@"; }
    ./csp5p 24 E self_tests/boxtest_in.txt point_placement/src/octdod.txt | norm      # = norm self_tests/exp_csp_E.txt
    PLANT=11 COUNT=1 ./csp5p 24 E self_tests/boxtest_in.txt point_placement/src/octdod.txt | norm   # = exp_csp_PLANT.txt
    ./gtestS E self_tests/boxtest_in.txt | grep '^code ' | norm                          # = exp_gt_E.txt
    ./gtestS P 0.285 11 | grep '^planted' | norm                                        # = exp_gt_P.txt
    ./gtestS Z 0.005 1 | grep '^sextetZ' | norm                                          # = exp_gt_Z.txt (31 999 solutions)
    (cd point_placement/cross_checks && ./gbfs zc_1.forb8.bin zc_1.forb12.bin)           # = zc_1.gbfs.out
    bash point_placement/planted_control/run_control.sh D    # D/kit/ holds csp5p_static_v3 (any build) and octdod.txt; D/tmp/ exists
    python3 point_placement/main_run/aggregate.py 13485816 point_placement/main_run/results/host{D,E,C}.out.tgz
                                                             # = point_placement/main_run/results/aggregate_final.txt
    python3 octad_growth/main_run/covcheck.py octad_growth/main_run/results/hostB octad_growth/main_run/results/x
    python3 octad_growth/main_run/covmanifest.py octad_growth/main_run/results/hostB octad_growth/main_run/results/x
    (cd point_placement/cross_checks && python3 compare2.py results/rand1200 .gt9 && python3 compare_pz2.py results .gt4)

We ran all of these on a rebuild from the files of this archive, and they reproduce the shipped records. So do
`symchk validation/rank11.txt` (= `symchk.out`), `lab16 codes16.txt` and `chk` (length-48 test), `mkg24`
(= `validation/g24f4.txt`), `dcirc` (= `cross_checks/dcirc_d8.txt`), `raw2compact` on `validation/z_1.*`
(= `cross_checks/zc_1.*`), and `csp5p_plantdump` with `DUMPF` and `PLANT=101` on `code_1234567.txt`
(= `p_1234567_s101_*.bin` and `u_1234567_*.bin`). The cross-check launch scripts expect the directory layout of the
original runs (the point-placement executable in `../../../prod_v1/`, the gtest sources in `gt4src/` and `gt9src/`).

### The main runs

Point placement: each line of the class list was given the suffix ` id=<0-based line number>`, the list was cut into
six consecutive parts whose concatenation is the list, and each machine ran
`run_list.sh WORKDIR PART NWORKERS 200` (parts of 200 classes, resumable). The id ranges of the three machines are
listed in `COVERAGE_PROOF.txt`; they partition [0, 13 485 816). The parts can be regenerated from the class list,
for example the last part (`reserve_3`):

    gzip -dc cls24.txt.gz | awk '{print $0 " id=" NR-1}' | tail -n 450000 | sha256sum   # = reserve_3 in shares/DECOMP_SHA256.txt

Octad growth: `gtestS R codes.txt S NS START` tests the lines i with i mod NS = S and i >= START in increasing order,
prints a progress line with the last index every 200 classes and `FINISHED` at the end. The classes with index below
3 600 000 were run in 300 slices (NS = 300, START = 0; stopped by `stopper.sh` once past 3 600 000), the others in
740 slices (NS = 740, START = 3 600 000; run to `FINISHED`).

### Run records

Main runs of the two labelling programs:

| Check | Outcome |
|---|---|
| Environments of all running main-run processes (both programs), read on the machines during the runs and checked for diagnostic switches (four times for the point-placement program, so that every process was covered). | no switch set |
| Self-tests of the main-run executables on all six machines that ran them, during the runs and again afterwards: fixed instances with known outputs, among them planted codes and a sextet instance with 31 999 solutions. | outputs identical to the expected ones in every test |
| Point-placement program in its main-run environment, after the run, on its three machines: 3 real classes with a planted Golay code, and the same 3 classes without it. | every planted code found; no solution without it, with the main-run node counts |

Octad-growth main run, slice coverage records:

- The 300 slices passed the end of their range and were then stopped, and the 740 others finished.
- The 60 000 classes with indices 3 600 000 to 3 659 999 were decided a second time by the first group of slices.

The last environment check, at the end of the point-placement run, is line 10 of `self_tests/SUMMARY_final.txt`; the
others are in `process_checks/`. The self-tests are summarised in `self_tests/SUMMARY_mid.txt` (during the runs) and
`SUMMARY_final.txt` (after them), and the planted test after the run in `point_placement/planted_control/EXPECTED.txt`
and `box_results/`. `octad_growth/main_run/MANIFEST.txt` and `COVERAGE.txt` record the per-slice checks and the
60 000 classes decided twice.

### Checks of Theorem B

Paths are relative to `order3/labelling/`, except those that begin with `order3/`.

| Check | Outcome | Files |
|---|---|---|
| Main run of the point-placement program on all 13 485 816 classes (4.37 x 10^14 nodes), with its coverage checked by two independent programs. | No valid Golay code for any class. All 13 485 816 classes covered, none missing or duplicated; no decision concerns a class outside the list; no errors reported. For each class the program's count of words of weight 8 up to scalars equals A8/3, and the code it tested agrees with the list (compared by hashes). | `point_placement/main_run/results/` (per-class lines and `aggregate_final.txt`); in `point_placement/main_run/`: `COVERAGE_PROOF.txt` (items 2 and 3: each machine's inputs hashed against the list lines of its ranges, and the per-line check of A8/3), `inputsha_host*.txt`, `cls24sha_host*.txt`, `strict_host*.txt`, `LEDGER.tsv`, `RUNPLAN.md`; second checker `order3/cross_check/src/cov_csp.py`, `order3/cross_check/cov/csp_cov_final.txt`, `csp_status_final.txt` |
| Main run of the octad-growth program on all 13 485 816 classes, with its coverage checked by two independent programs. | No solution. Each class decided exactly once, in the part to which it was assigned; no output other than these decisions. | `octad_growth/main_run/results/`; in `octad_growth/main_run/`: `MANIFEST.txt`, `COVERAGE.txt`, `covcheck.py`, `covmanifest.py`, `PROVENANCE.txt`; second checker `order3/cross_check/src/cov_gt.py`, `order3/cross_check/cov/gt_cov_final.txt`, `hostBrun1/`, `gtfinal/`, `gtp/` |
| Review of both labelling programs by the order-3 cross-check: inspection of the source code, an independently computed reference, and an independent solver, run on 5 711 classes, among them G24 (x) F4, all 3 862 classes with 9 <= abs(Aut_Mon) < 3 abs(M24) and all 225 with beta >= 94. | The independent solver finds no valid labelling for any of the 5 711 classes. | `order3/cross_check/prov/`, `rev_csp5p/`, `gth/`, `rev_gtestS/`; the independent solver's runs in `order3/cross_check/samp/` |
| Symmetry reduction of the octad-growth program for the two classes whose words of weight 8 span 11 dimensions (Sec. 7; abs(Aut_Mon) = 288, A8 = 513 and abs(Aut_Mon) = 9216, A8 = 837): the validity of the group used in the main run, and both classes re-tested without the reduction, with the main-run executable and with a variant that switches the reduction off when the words of weight 8 do not span the code. | Reduction valid; neither re-test finds a solution. | `octad_growth/validation/symchk.out` (from `octad_growth/src/val/symchk.c`: the reduction preserves all supports of weight 8, 10 and 12); `octad_growth/validation/rank11_prod_nosym.out` (main-run executable without the reduction); `octad_growth/rank11/rank11_gtestS.out` (a build with the span check of `octad_growth/src/gtestS.c`) |
| G24 (x) F4 (beta = 253), with its coordinates in random order and in the order of the reference Golay code, and as a double circulant code: point placement (1.52 x 10^9 nodes per run), a variant of the octad-growth program without the symmetry reduction, the octad-growth program with the reduction, and the independent solver without it (1.66 x 10^9 nodes, order-3 cross-check). | No run finds a solution. | point placement: `point_placement/cross_checks/results/struct/ch_000.csp`; octad growth with the reduction: `octad_growth/validation/g24f4s.out`; octad growth without the reduction (three runs of the earlier version gtest4): only the summary `point_placement/cross_checks/gtest4_reported` (the output files were not kept, and the runs, over four hours each on one core, were not repeated); independent solver: `order3/cross_check/samp/` (`sp_g24.*`) |

## Theorem D: no fixed-point-free involution (directory `order2/`)

Theorem D (Sec. 6) states that for each of the 41 self-dual [36,18,8] codes Y, no extremal code has a fixed-point-free
involution with contracted fixed code Y. Each code Y was decided by one exhaustive search, run as a package of parts
(Table 3).
Paths in this section are relative to `order2/`.

### Layout

| Directory | Contents |
|---|---|
| `codes/` | The 41 self-dual [36,18,8] codes, `codes36.txt`, numbered 0 to 40 in file order (Y0 to Y40); the file is identical to `klein/codes36.txt`. |
| `model/` | The instance generator and the record checkers. `model/explore/`: reduction and instance builder (`common.py`, `mkinst.py`, `mkinst_c.c`), symmetry files (`symprep*.py`), and the checkers of the run records (`partcheck.py`, `fleet_prov.py`, `xcheck_cmp.py`, `xsplit_cmp.py`, `exclusion_table.py`, `excl_common.py`, `xcheck_own.py`, `gate_table.tsv`, `xcheck_policy.tsv`) with the wrappers `run_partcheck.sh` and `run_xcheck_cmp.sh`. `model/struct/`: the package builder (`src/`), the frozen builder files listed in the `INPUTS.sha256` of the packages and of the runs (`frozen/`), and the build record of every package (`records/`). |
| `engines/` | The search programs. For each version a directory with its frozen sources, build script, `BUILD.sha256` and `FROZEN.sha256`, and the executables used in the main runs: `lwe8_reference/` (the reference program), `rc7/`, `rc9/`, `rc11/`, `rc13/`, `rc14/`, `rc14g/<run>/` (builds generated for one run each), `b/`, `b3/`, `b5/`, `b7/` (the builds lwe11b, lwe11b3, lwe11b5, lwe11b7 for processors without AVX-512). `BINARIES.sha256` lists the 21 executables; their sha256 are those recorded for every part in `runs/<run>/ENGINES.txt`. `explore/`: the sources of the programs of the eight runs made outside the package fleet (`lwe5.c`, `lwe8.c`, `lwe10.c`, `lwe11.c`), and the directories of lwe10, lwe11 and lwe11b as those runs used them (`frozen3/`, `frozen4/`, `frozen5b/`: source, build script, `BUILD.sha256`, check script), without executables. `validation/`: the identity suites against the reference program. `gate/`: the identity checks made before each program version ran in main runs. |
| `packages/<run>/` | The inputs of each package run as used: `INPUTS.sha256`, `PLAN.txt`, the instance (`inst.txt`, `inst.txt.meta`, `inst.txt.pkl`), the symmetry file (`sym.ltsh`; `sym.ltsb` for the runs with the bit-granular symmetry test), and the key and flag files. |
| `runs/<run>/` | The records of each package run: `parts.tar.gz` (one log per part), `SHA256SUMS` (sha256 of every part log), `ENGINES.txt` and `ORIGIN.tsv` (program, executable sha256 and machine of every part), `checks/` (box checks, with the repeated attempts in `checks/attempts/`), `xcheck/` (cross-check reruns, with `split/<part>/VERDICT.txt` for split ones), `BOX_GATES.txt`, `ENGINES_CHECKS.txt`, `COMPLETE`, `DUPS.tsv` with `dups.tar.gz` (second runs), and `summary/` (`RUN_SUMMARY.txt`, `SUMMARY.txt`, `PARTS_BY_ENGINE.txt`). |
| `runs/<code>/` | The eight runs made outside the package fleet (`y1b`, `y4`, `y5b`, `y8`, `y22`, `y23`, `y29`, `y39`): inputs, part logs (packed or, for `y39`, as plain files), summaries, cross-check reruns. `runs/y39/inputs/` holds the instance files and program source listed in its `INPUTS.sha256`. |
| `certificate_y39/` | The parity certificate that excludes Y39 without a search, its checker and its verification logs. |
| `independent/` | The independent re-searches of Y8, Y18, Y22, Y23 and Y39: sources, reports and outputs. |
| `cross_check/` | `coverage/`: the coverage checker of the 41 runs with its reports, the reference builds for the prefixes, the symmetry-file checks and planted tests, and deliberately broken records. `engines/`: the comparisons of the search programs with the reference program and with a naive search, the split-sum tests, the instance checks of all 41 runs. |
| `controls/` | Tests on known codes: the extended quadratic residue codes of lengths 48 and 72. |

### The 41 runs of Table 3

The parts of a run split its search as described under "Conventions in the records". For each code the order of the
basis w_0, ..., w_17 was chosen by beam search and hill climbing on an estimate of the number of nodes, in some cases
starting from a small Aut(Y)-invariant subspace. The first symmetry test uses the symmetry file `sym.ltsh` of the
package. For the first component the program computes s_{k0 g}(B) only once for each coset Gamma0 g of the stabiliser
Gamma0 of k0 in Gamma, takes from a precomputed table the smallest of the values s_{k0}(B^h) = T_{h,k0} s_{k0 g}(B)
for h in Gamma0 g, removes the node if this value is smaller than s_{k0}(B), and compares the later components only
for the h with s_{k0}(B^h) = s_{k0}(B) (`lh_reject` in `engines/lwe8_reference/lwe8.c`).

Every code is decided by one complete run with 0 solutions. Run names are the directory names under `runs/`. "Cross-check" is the
number of seeded parts rerun with the reference program on another processor family and found identical.

| Code | Run | Parts | Core-hours | Programs (parts) | Cross-check | Independent re-search |
|---|---|---|---|---|---|---|
| Y0 | `runs/y0-lb/` | 64 000 | 168 649.8 | lwe11b7 2 983, rc13 61 017 | 8/8 | - |
| Y1 | `runs/y1b/` | 8 000 | 704.9 | lwe11 native, lwe10/lwe11 portable | 8/8 | - |
| Y2 | `runs/y2/` | 16 000 | 3 742.9 | lwe11b3 87, rc9 15 913 | 8/8 | - |
| Y3 | `runs/y3/` | 32 000 | 4 332.0 | lwe11b3 193, rc9 31 807 | 8/8 | - |
| Y4 | `runs/y4/` | 4 000 | 773.4 | lwe8 native 3 640, lwe11 360 | 8/8 | - |
| Y5 | `runs/y5b/` | 4 000 | 85.4 | lwe11 native | 8/8 | - |
| Y6 | `runs/y6/` | 16 000 | 2 187.1 | lwe11b3 35, rc9 15 965 | 8/8 | - |
| Y7 | `runs/y7/` | 16 000 | 2 653.7 | lwe11b3 57, rc9 15 943 | 8/8 | - |
| Y8 | `runs/y8/` | 500 | 17.1 | lwe8 | 8/8 | `independent/y8/` |
| Y9 | `runs/y9/` | 16 000 | 3 341.2 | rc7 16 000 | 8/8 | - |
| Y10 | `runs/y10b/` | 8 000 | 1 400.5 | rc7 8 000 | 8/8 | - |
| Y11 | `runs/y11b/` | 4 000 | 1 117.9 | rc7 4 000 | 8/8 | - |
| Y12 | `runs/y12-lb2/` | 64 000 | 287 302.5 | lwe11b7 2 847, rc13 49 186, rc14g (Y12 build) 11 967 | 8/8 (split) | - |
| Y13 | `runs/y13/` | 32 000 | 4 013.7 | lwe11b3 101, rc9 31 899 | 8/8 | - |
| Y14 | `runs/y14-lb/` | 64 000 | 146 462.3 | lwe11b7 3 774, rc11 535, rc13 59 691 | 8/8 | - |
| Y15 | `runs/y15-lb/` | 64 000 | 479 979.6 | lwe11b7 2 677, rc14g (Y15 build) 61 323 | 8/8 (split) | - |
| Y16 | `runs/y16b/` | 1 000 | 744.5 | rc7 679, rc9 321 | 8/8 | - |
| Y17 | `runs/y17/` | 4 000 | 982.4 | rc7 4 000 | 8/8 | - |
| Y18 | `runs/y18c/` | 1 000 | 138.1 | rc7 1 000 | 8/8 | `independent/y18/` |
| Y19 | `runs/y19b-lb/` | 64 000 | 37 280.4 | lwe11b7 3 378, rc13 60 622 | 8/8 | - |
| Y20 | `runs/y20b-lb/` | 64 000 | 21 119.7 | lwe11b5 3 504, rc11 60 496 | 8/8 | - |
| Y21 | `runs/y21/` | 16 000 | 4 810.0 | lwe11b 104, rc7 12 341, rc9 3 555 | 8/8 | - |
| Y22 | `runs/y22/` | 4 000 | 414.0 | lwe8 native | 8/8 | `independent/y22/` |
| Y23 | `runs/y23/` | 4 000 | 237.6 | lwe10 native | 8/8 | `independent/y23/` |
| Y24 | `runs/y24b/` | 1 000 | 256.8 | rc7 1 000 | 8/8 | - |
| Y25 | `runs/y25/` | 64 000 | 7 271.8 | lwe11b3 426, rc9 63 574 | 8/8 | - |
| Y26 | `runs/y26f-lb/` | 64 000 | 81 640.2 | lwe11b7 3 523, rc13 60 477 | 8/8 | - |
| Y27 | `runs/y27b/` | 2 000 | 577.0 | rc7 2 000 | 8/8 | - |
| Y28 | `runs/y28s/` | 4 000 | 699.2 | rc7 4 000 | 8/8 | - |
| Y29 | `runs/y29/` | 4 000 | 5 625.7 | lwe10 860, lwe11b 3 140 | 20/20 | - |
| Y30 | `runs/y30/` | 64 000 | 20 784.8 | lwe11b3 1 090, rc7 215, rc9 62 695 | 8/8 | - |
| Y31 | `runs/y31/` | 8 000 | 1 944.5 | rc7 8 000 | 8/8 | - |
| Y32 | `runs/y32-lb/` | 64 000 | 39 530.0 | lwe11b5 2 059, rc11 61 941 | 8/8 | - |
| Y33 | `runs/y33/` | 2 000 | 279.3 | rc7 2 000 | 8/8 | - |
| Y34 | `runs/y34/` | 64 000 | 19 307.6 | lwe11b3 422, rc7 106, rc9 63 472 | 8/8 | - |
| Y35 | `runs/y35/` | 4 000 | 3 496.6 | lwe11b3 12, rc9 3 988 | 8/8 | - |
| Y36 | `runs/y36/` | 16 000 | 2 796.7 | rc7 16 000 | 8/8 | - |
| Y37 | `runs/y37/` | 16 000 | 3 250.6 | lwe11b3 114, rc9 15 886 | 8/8 | - |
| Y38 | `runs/y38/` | 8 000 | 1 552.9 | rc7 8 000 | 8/8 | - |
| Y39 | `runs/y39/` | 2 000 | 11.3 | lwe5 | 6/6 reruns (see the checks) | `independent/`; `certificate_y39/` |
| Y40 | `runs/y40/` | 64 000 | 222 570.8 | lwe11b7 3 002, rc13 58 849, rc14g (Y40 build) 2 149 | 8/8 (split) | - |

The node counts of Table 3 follow from each run's part logs, through the LEVEL lines of `summary/RUN_SUMMARY.txt`,
counted as described under "Conventions in the records". The core-hours column is the sum of
the times on the DONE lines of a run's part logs (the "CPU seconds" line of its summary; each part ran as one
single-threaded process); the total over the 41 runs is under "Running times" below.

### Checks of Theorem D

The cross-checks of the 41 searches use code written for them, which shares no code with the programs it checks apart
from the search programs under test. Three checkers rerun on the files of this archive:
`cross_check/coverage/run_coverage.sh`, `model/explore/run_partcheck.sh` and `model/explore/run_xcheck_cmp.sh` unpack
the part logs into a work directory and compare their output with the shipped records (see "Rerunning the checks"
below). No independent search was made for the 36 codes other than Y8, Y18, Y22, Y23 and Y39; for them the checks
below test the instance files, the program versions and the coverage of the runs, and rerun selected parts with the
reference program.

| Check | Outcome | Files |
|---|---|---|
| Instance files of all 41 runs, as run (checked by sha256 against `INPUTS.sha256`): every constraint row, bad set and level derived independently and compared with the file searched; the symmetry data recomputed from their definitions (for Y39 its earlier symmetry table), and the identity s_w(B^g) = T_{g,w} s_{wg}(B) of Sec. 6.2 tested on random forms B and elements g. | Files identical to those searched, with one constraint for each word of weight 8, 10 and 12, no word of weight 14 able to violate its condition, dim G0 = 35 and an injective parametrisation; all 41 pass. | `cross_check/engines/scripts/indep_c2.py`, `symcheck.py`, `symcheck1.py` (Y39); logs in `cross_check/engines/pkgcheck/` (`batch1.out`, `logs/`) |
| End-to-end test of the reduction: 410 codes C_B, for ten random forms on the instance of each run, built with all their words of weight at most 14; for the same forms, the code of B + D_T compared with the swapped code C_B s_T (Sec. 3.3), and the code of B^g with the image of C_B under the lift of g^-1 for g in Aut(Y) (Sec. 6.2). | Each of the 175 195 violated constraints has a word of weight below 16 over its word y; none of the 4 743 085 satisfied constraints has one; the compared codes are equal. | `cross_check/engines/scripts/e2e_c2.py`; logs in `cross_check/engines/pkgcheck/` |
| Earlier round of the instance and end-to-end checks: the end-to-end test on 63 instances covering the codes Y0 to Y38 and Y40 (10 random forms each), with gauge moves and lifts of automorphisms of Y applied to the explicit codes, and the instance files and symmetry data of 68 packages. | 630 codes: 269 275 violated constraints, each with a word of weight below 16; 7 300 445 satisfied without one. Every gauge move and every lift gives the expected relabelled code (630 of 630 each). All 68 packages and the Y39 instance agree with their definition. | `cross_check/engines/logs/e2e/`, `logs/indep/`, `logs/sym/` |
| The search programs against the reference program, on parts of real instances and on pinned sub-instances (exact, relaxed and planted, with and without symmetry): without the bit-granular symmetry test against lwe8, with it against lwe10b; rc14 and the three package-specific rc14g builds against rc13 and the reference; lwe8 without symmetry against a naive search. The executables were rebuilt from their sources. | 0 differences and 0 timeouts in 65 582 runs without the bit test, in 1 568 runs with it, in 585 runs of rc14 and 195 per rc14g build, and in 5 710 tests against the naive search. Every executable rebuilt byte for byte. | `cross_check/engines/scripts/difftest_c2.py`, `core_test.py`, `pin.py`, `pinltsb.py`, `naive.c`, `lwe8_ref.c`; drivers and task lists in `cross_check/engines/boxkit*/`; logs in `cross_check/engines/boxlogs/`, `logs/` (`final_summary.txt`, `final6_summary.txt`, `diff_*.log`), `rc14/`, `build_*/` |
| Splitting: the parts of a run partition the nodes that survive at the split level, in every program version. Each check sums the parts of a split run and compares the sums with the unsplit run, level by level and for the solution sets. | 16 367 split-sum checks, 336 of them with the bit test at split levels where it prunes, all equal; the split-level count check is equal on 15 codes. | `cross_check/engines/scripts/pin.py`, `pinltsb.py`, `logs/lbpin/`; `cross_check/coverage/splitsum/` |
| The symmetry argument (Lemma 6.3) on real instances, flags, keys and symmetry files: runs with one planted member of an orbit and runs with a whole planted orbit. | Every K-minimal member is kept, in 1 553 single-member runs and in 805 whole-orbit runs, among them an orbit of 864 on Y23 with a tie of 432 members, kept with identical output by all seven programs; 1 524 non-minimal members are pruned. | `cross_check/coverage/plant/`, `boxkit_results.txt` (the tie on Y23) |
| The symmetry files of the eight runs with the bit-granular test: each checked against its definition, planted runs, and mutated files that must fail. | All eight pass (288 single-member and 216 whole-orbit planted runs); the mutated files fail. | `cross_check/coverage/ltsbcheck.py`, `ltsbcheck_<run>.txt`, `ltsbplant.py`, `ltsbplant_<run>.txt`, `lbgate.sh`, `negctl_ltsb/`, `negctl_ltsbplant_result.txt` |
| Derived constraints (projected bad sets added to some test instances): soundness of every derived constraint. | Sound in all 18 augmented instances. Planted end-to-end tests on Y29 pass; an unsound mutant fails. | `cross_check/engines/scripts/derchk.py`, `logs/der/`; `cross_check/coverage/der/` |
| Coverage of each run, by the coverage checker, under the conditions listed after the table. Deliberately broken records (a removed part, a changed input, a wrong executable, a failed check) must make the check fail. | All 41 runs pass; every deliberately broken record makes the check fail. | `cross_check/coverage/cov_c2.py`, `cov_all.sh` (as run), `run_coverage.sh` (on this archive), `cov_<run>.txt`, `prefix_<run>.txt`, `lwe8_ref.c` and `lwe10b_ref.c` (the reference builds for the prefixes), `xsplit_agg.py`, `checklog_eval.py`, `refreuse_checklog_eval.txt`, `cov_negctl_*.txt`, `negctl*/` |
| Part logs of each run: the structure of every part log and the identical prefix in all parts. | All 40 runs other than Y39 pass partcheck (the run of Y39 predates this check; its coverage report covers its part logs). | `model/explore/partcheck.py`, `run_partcheck.sh`; `runs/<run>/summary/RUN_SUMMARY.txt` |
| Cross-check reruns: 8 seeded parts per run (part i = sha256("c2-xcheck-" + run + "-" + i) mod NPART), each rerun with the reference program on another processor family and compared line by line without times; for Y40, Y12 and Y15 split cross-checks in 16, 16 and 32 sub-parts; for Y29 the 20 parts rerun with lwe8 when its program was admitted. | All identical: 8 of 8 for every run (for Y40, Y12 and Y15 as split cross-checks, with 16, 16 and 32 sub-parts), 20 of 20 for Y29, and 48 of 48 for the six runs made outside the fleet, which were rerun on another processor family. | `model/explore/xcheck_cmp.py`, `xsplit_cmp.py`, `xcheck_policy.tsv`, `run_xcheck_cmp.sh`; `runs/<run>/xcheck/` (with `split/<part>/VERDICT.txt`), `runs/<code>/XCHECK8.txt`, `runs/y29/XCHECK_GATE20.txt` |
| Box checks and second runs, as described under "Run records" below. | Every machine that produced a counted part has a passed check; every second run is identical to the stored part. | `runs/<run>/checks/`, `checks/attempts/`, `BOX_GATES.txt`, `ENGINES_CHECKS.txt`, `DUPS.tsv`, `dups.tar.gz`; `model/explore/fleet_prov.py`; `runs/<code>/RUN_SUMMARY.txt` and `RUN_LOCAL.txt`, `runs/y29/checks/`; the check scripts `check_box.sh` in `engines/lwe8_reference/` and `engines/explore/frozen3/`, `frozen4/`, `frozen5b/` |
| Admission of program versions: the parts of a main-run program counted only after the program had been compared with the reference program on seeded parts of the runs. | rc7 and lwe11b identical to lwe8 on 60 of 60 parts, rc9 on 20 of 20 (Y29); the later versions were admitted under the same rule (see "Run records"). | `engines/gate/`, `engines/validation/` |
| Reruns of the runs made outside the fleet with independently built reference executables, whole parts. | 13 of 13 identical across every executable class; for Y39, parts 1674, 253 and 1971 rerun with its earlier program and with lwe8 under the same symmetry file: 6 of 6 identical. | `cross_check/coverage/xnat/` (`results.txt`, `out/`) |
| The 32-bit counter of lwe8's symmetry cache. | Every main-run part of lwe8 stays below 15 % of 2^32 node entries (largest 6.4e8, Y4), so the counter cannot wrap there; it wraps only in reference reruns of the largest parts, where the worst effect would be a false difference, and none occurred. | `cross_check/coverage/maxnodes.py`, `maxnodes.txt` |
| Parity certificate for Y39, without a search: a count, defined after the table, that must be odd for every form B, evaluated at the 3 660 967 171 points of Hamming weight at most 6, twice, in different coordinates, by a checker written for the purpose. | Odd at all points in both verifications, so every form violates a constraint; for Y0 and for the code Y of QR48 the same check finds even values, as it must. | `certificate_y39/` (`csrc/parcheck.c`, `mkpar.py`, `mkpar2.py`, `verify_par.py`, `xcheck_par.py`, `data/par_y39_x12b.txt`, `data/par_y39_x12b_v2.txt`, `logs/par39/`, `logs/par39v2/`; the controls `data/par_y0_x12b.txt`, `data/par_qr48_all.txt` with `logs/cite39/negctl_*.txt`) |
| Independent re-searches of Y8, Y18, Y22, Y23 and Y39 by a program written from a statement of the problem. On the length-48 test it runs without its orbit reduction and with a reduction by a subgroup of order 120. | No solution; nodes about 9.1e10 (Y39), 9.43e11 (Y8), 6.988e13 (Y18), 1.914e13 (Y22) and 2.195e12 (Y23); every kept value searched exactly once. Length-48 test: 5 760 solutions without the reduction, among them the form of QR48; with the reduction, the images of its 116 solutions are these 5 760. | `independent/` |
| Known codes: the extended quadratic residue codes of lengths 48 and 72. | QR48: 5 760 solutions including the code's own form, 100 sampled solutions rebuilt as genuine [48,24,12] codes; with symmetry, the orbit closure of the kept solutions is exactly the 5 760 for the full group (order 138 240), a point stabiliser, a cyclic subgroup of order 6 and non-prefix keys. QR72 with pinned levels below 12 and below 10: 500 and 607 246 solutions, the own form among them. | `controls/` |

In the comparisons of the search programs with the reference program, a run gives the same input to several programs, so
the runs per program add up to more than the number of runs. Without the bit-granular test: rc7 29 909, lwe11b 52 985,
rc9 19 589, lwe11b3 19 104, lwe10 and lwe11 7 400 each, rc11 18, lwe11b5 20, and rc13 and lwe11b7 388 each. With it:
rc11 684 and lwe11b5 711, and rc13, lwe11b7 and rc11 in 857 runs.

The coverage checker requires, for each run: every part present once and complete with all its levels and no solution;
the inputs equal to `INPUTS.sha256`; for package runs, an admitted executable for every part and a passed box check for
every (machine, program) pair; the levels up to the split identical in all parts and equal to a run of the reference
program; and the same manifest of the part logs from the checker and from the aggregation of the runs, which repeats the
part checks.

The parity certificate: for every form B, the number of pairs (y, e) with abs(y) = 8, abs(e) = 2, e disjoint from supp y
and (<e, x_j>)_j = s_y(B), plus the number of words y of weight 12 with s_y(B) = 0 (X8b + X12 in the files), is odd.
This number is a polynomial of degree at most 6 in affine coordinates on the 119-dimensional space of cosets of G0:
s_y(B) is affine in B, and its value at 1+y is B(y, 1+y) = abs(y)/2 for every form, so the term of a word of weight 12
is a product of 6 affine forms; `certificate_y39/verify_par.py` finds degree at most 6 for every term
(`certificate_y39/logs/cite39/verify_par_x12b.txt`). So it suffices to evaluate it at the points of Hamming weight at
most 6.

The independent program: Aut(Y) acts by affine maps on the values of 31 to 40 linear functions B(x, x') with x and x'
disjoint. The program keeps the smallest value in each orbit that passes the constraints these functions decide, with
further reductions by subgroups that fix the value for three of the codes, and completes the form by a depth-first
search.

#### Rerunning the checks

The three wrappers need Python 3 (`PYTHON` may name another interpreter) and leave the archive tree unchanged:

    bash order2/cross_check/coverage/run_coverage.sh -o OUT y18c y40 y8      # or: all
    bash order2/model/explore/run_partcheck.sh -o OUT y18c y40              # or: all
    bash order2/model/explore/run_xcheck_cmp.sh -o OUT y18c y40            # package runs

`run_coverage.sh` reruns `cov_c2.py` with the shipped prefix files and compares each new report with the shipped one;
on the files of this archive the reports are identical except for directory paths. One input file listed in the
`INPUTS.sha256` of the eight runs with the bit-granular test, `tools/mklb.sh`, contained home paths, which we replaced
for publication; `cov_redacted.py` accounts for the change through `REDACTIONS.tsv`. `run_partcheck.sh` and `run_xcheck_cmp.sh`
compare their summary lines with the run summaries recorded at the time of the runs.

### Checking a package

For a package run `<run>`, in a copy of the archive:

    cd order2/packages/<run> && ln -s ../../model/struct/frozen frozen && sha256sum -c INPUTS.sha256
    cd order2/runs/<run> && tar -xzf parts.tar.gz && sha256sum -c SHA256SUMS

The first command checks the inputs (the frozen builder files listed in `INPUTS.sha256` are in `model/struct/frozen/`);
for the eight runs with the bit-granular test it reports a mismatch for `tools/mklb.sh` (see "Rerunning the checks").

### Notes on the files

- `inst.txt.pkl` in each package is a Python pickle cache that the builder writes together with `inst.txt`. We
  ship it because `INPUTS.sha256` lists it. The builder writes both again:
  `python3 -I model/struct/frozen/prep_code.py CI packages/<run>/flag.txt KEYSPEC OUT`, with CI and KEYSPEC as on the
  BUILD line of the package's `PLAN.txt`; compare `OUT/INPUTS.sha256` with the package's. Verify the sha256 of a pickle
  against `INPUTS.sha256` before loading it, since loading a pickle runs code. For
  the package y33 the command rebuilds all six files with the same sha256 (5 seconds; Python 3 with numpy).
- `runs/<run>/checks/attempts/` contains the 60 box-check attempts that did not complete: some
  stopped on a fault of the check script (it looked for the program at a wrong path), the others were interrupted. For
  every one of them the same check on the same machine was run again and passed; the passed log has the same base
  name in `checks/`.

### Run records

- Admission of program versions: the comparisons of rc7, lwe11b and rc9 with lwe8 on seeded parts of the runs of Y28,
  Y17 and Y29 were made on 2026-10-21, while the first main runs, which began that day, were under way. lwe11b3 shares
  rc9's decision code and passed the identity suites. rc11 and lwe11b5, with the bit-granular symmetry test, were
  identical to the prototype lwe10b on 40 of 40 parts, and passed the identity suites and the planted tests; a run with
  them counts only if its symmetry file passed its own check and planted tests, every machine that produced parts
  passed a full box check with both identity steps, its 8 cross-checks with lwe10b and the symmetry file were
  identical, and the part-log check and coverage passed. rc13 and lwe11b7 are byte-identical drop-ins for rc11 and
  lwe11b5 (2026-10-22); rc14 and the three rc14g builds, each valid only for its own run, entered the main runs on
  2026-10-24 under the same rule.
- The reference program of the cross-checks is lwe8 for the runs without the bit-granular test, lwe10 (lwe10b without a
  symmetry file) for Y40, whose parts exceed the range of lwe8's 32-bit counter, and lwe10b with the symmetry file for
  the runs with the bit test. A split cross-check in m sub-parts reruns part k as the parts k + NPART j, j = 0, ...,
  m - 1, of a split into m NPART parts; their counts must sum to the counts of part k.
- Box checks: before its parts counted, each machine ran a check of its program on one part (part 17 of a finer split of
  the run's split level, into 200 000 or 20 000 000 parts): inputs, frozen sources, executable sha256, a probe estimate,
  and for a full check a comparison with the reference program. A full check was made at least once per machine family
  and program; in three runs, other machines of that family ran a light check without the comparison. For the runs
  with the bit-granular test every machine needed a full check. A check could reuse the identity reference computed on
  another machine for the same part. A machine could produce parts while its check ran; its parts count once the check
  has passed, also when it passed after the machine's last part (`BOX_GATES.txt` gives the time of each check).
- Second runs: a part produced on a machine without a passed check, or whose record carries an environment tag or a
  measured executable that differs from the admitted one, counts only through a second run on a checked machine with
  an identical log (`DUPS.tsv`, `dups.tar.gz`): 3 016 parts of Y14, 5 653 of Y0 (including part 32901 of Y0, whose first
  run carried an environment tag), 88 of Y40 and 176 of Y12. Some runs also have second runs that were not needed, for example 294
  of Y3. The `note: second runs` line of each coverage report records the comparison of all second runs with the
  stored parts.
- The six single-machine runs (Y1, Y4, Y5, Y8, Y22, Y23): their cross-checks were made on 2026-10-22 with the portable
  build of lwe8 on a machine of family famF (`runs/<code>/xcheck/`, `XCHECK8.txt`). Their box checks, and those of
  Y29, are described with the gaps in their records under "Box-check records of Theorem D"
  (in "Provenance of the files and records").
- The run of Y39 predates the box checks.

## Running times

The wall-clock times of the parallel parts of the order-5 search sum to 232 372 s (64.5 hours, about 516
thread-hours), and the independent implementation of Theorem A ran for 22.1 CPU-hours. For Proposition 3.8, Implementation I
took 288 835 CPU-seconds in total, and Implementation II took 131 678 CPU-seconds in its first run and, in its second
run, 134 550 CPU-seconds for the five largest instances and 5 200 CPU-seconds for 111 others. The third solver took
3 889 321 CPU-seconds in total. For Theorem B, the per-class wall-clock times of the point-placement program sum to
68 507 615 s (5.08 s per class), and the slowest class, G24 (x) F4, took 2 274.3 s. The octad-growth run took about
17 700 CPU-hours. On G24 (x) F4, a variant of the octad-growth program without the symmetry reduction took 15 336 to
15 803 s per run, and the octad-growth program with the reduction took 63 s. For Theorem D, the wall-clock times of the
parts of the 41 searches, each part one single-threaded process, sum to 1 584 087 hours. The
independent program of Theorem D took about 6 000 core-hours for its five codes.

## Tests of individual components

This section lists the tests of individual components, in three parts: Theorem A, Proposition 3.8, and Theorems B
and C. A tag such as "(order-5 cross-check)" marks a test made with the code of that cross-check: the order-5
cross-check of Theorem A (`order5/cross_check/`), the third-solver cross-check of Proposition 3.8 (`klein/checks/gd/`)
or the order-3 cross-check of Theorems B and C (`order3/cross_check/`).

### Theorem A

| Check | Outcome | Files |
|---|---|---|
| Explicit model (Sec. 2.1, Lemma 2.2), built by two independent programs: for random unitary U, dimension 36, self-orthogonality, double evenness and g-invariance of the binary code of length 72; on random codewords, the minimum binary weight over the 256 words of e8 + e8 against M(c_A) + M(c_B). | Properties hold; the two values are equal. | `order5/reference/model.py`; `order5/cross_check/sym72.py`, `sym72.out` |
| Symmetries (a)-(c) on explicit codes, four random U each: the code of the transformed matrix must be the image of the original code under the matching permutation, which fixes phi_0(e8 + e8) and normalises <g>. Also run on a transposition of two cycles of A that is not a collineation, where the test must fail. | (a)-(c) pass; the transposition fails, as required. | `order5/cross_check/sym72.py`, `sym72.out` |
| Brute-force recounts at 136 nodes on random paths (100 at threshold 16, 36 at threshold 12, where paths reach six rows): the number of children against a count over all 2^28 vectors that tests each word directly. This tester shares tables and symmetry rules with the search. | Equal counts at all 136 nodes. | `order5/search/tester.c`; `order5/logs/validation/hostB/t16.err`, `t12.err` |
| The same comparisons with new random choices: 392 at thresholds 16, 14 and 12 (240, 80, 72) (order-5 cross-check). | No difference in the 392 comparisons. At 14 the counts equal those at 16, since each tested word is isotropic and its minimum weight is divisible by 4. | `order5/cross_check/runs/t16.err`, `t14.err`, `t12.err`, `chainA.sh`, `chainB.sh` |
| Planted matrices: 200 random unitary matrices that satisfy the condition at threshold 12, put into normal form by independently written code and passed to the search (a test of the normal form, not of the pruning at 16); and 11 matrices that the independent implementation planted itself, searched for in 17 runs. | All 200 accepted at every depth; the independent implementation finds all 11 of its own. | `order5/search/planted2.c`, `order5/logs/validation/hostB/pl2.err`, `order5/cross_check/runs/p12.err` (a rerun, 40 of 40); `order5/independent_implementation/src/planted.c`, `src/planted_test.sh`, `results/host*/logs/planted_t12_*` and `pt_12_*.txt` (the 17 runs; the record of an 18th run, with seed 22 and one forced row, was not kept; `pt_s11_g2.txt` is an earlier run with seed 11) |
| M of Sec. 2.3 with its field tables, on all 16 384 patterns, against two independent implementations (packed pattern index, Hermitian product and scalar multiplication also against one of them on 20 000 random inputs); evenness of M and M(v) >= 2 for v != 0, on all patterns. | All values agree; both properties hold. | `order5/search/selftest.c`, `tables_c.txt`, `order5/reference/xcheck_tables.py`, `order5/cross_check/cmp_mtab.py`; `order5/search/unit.c`, `order5/reference/unitcheck.py`; `order5/cross_check/indep_patterns.py` |

### Proposition 3.8

| Check | Outcome | Files |
|---|---|---|
| Lemma 3.5(b) on four instances: s_T b s_T = ab for a transversal T, and C_B s_T = C_{B+D_T} for random B, again self-dual, doubly-even and invariant under a and b. | Both hold. | `klein/impl2/check_gauge.py`, output `klein/impl2/check_gauge.out` (regenerated on 2026-10-23) |
| Number of solutions at length 48 with the 17-dimensional span alone. | 192 and 128, mapping 2-to-1 onto the 96 and 64 solutions obtained with G. | `klein/impl2/check_gauge.out`; the 96 and 64 solutions with G also in `klein/impl2/control48.log` |
| Second generation of 8 instances of the third solver (third-solver cross-check). | Identical to the instances used. | `klein/checks/gd/scripts/e2e_check.py`; `klein/checks/gd/e2e/`, `local_inst_md5.txt`, `box_inst_md5.txt` |
| Instances of the third solver: self-duality, double evenness and invariance under a and b of explicit codes for random forms; for every constraint word and its image under beta, the decision against the true coset minimum over all 2^18 words of Y (about 60 000 good and 670 bad decisions per instance); all 2 909 364 syndrome forms of 25 instances and the bad sets of 204 sampled words (138 720 syndromes), recomputed (third-solver cross-check). | Properties confirmed; the instance files match every recomputed decision, syndrome form and bad set. | `klein/checks/gd/scripts/e2e_check.py`, `e2e_exact.py`; `klein/checks/gd/e2e/`, `e2e_exact.log` |
| Minimum weights of the extended quadratic residue codes of lengths 48, 72 and 80. Each code is built from an irreducible factor of degree (p-1)/2 of the p-th cyclotomic polynomial over F2 (p = 47, 71, 79) and checked to be doubly-even and self-dual. All sums of at most T+1 rows of the generator matrix in standard form on one information set, and of at most T rows on a disjoint one, are enumerated (T = 5, 5, 7). Every word of weight at most 2T+1 is visited, and every word of weight 2T+2 exactly once. | No word of weight at most 11, 11, 15; A_12 = 17 296 and 2 982, A_16 = 97 565. The first value agrees with Implementation II. | `klein/qrcheck/` (`qrgen.py`, `qrmin.c`, `qr48.txt`, `qr72.txt`, `qr80.txt`, `RESULTS.txt`, `SHA256SUMS`) |
| Test at length 48: complete searches, every solution rebuilt as a code and checked on all 2^24 codewords. Implementation I finds 64 solutions. Implementation II ran for two classes of Klein four-groups, with three choices of a each. The third solver finds 128 = 2 x 64 solutions. The form of the quadratic residue code was checked against the constraints. | Implementation II: 96 or 64 solutions per run. Every rebuilt code is doubly-even self-dual [48,24,12] with a, b among its automorphisms. The code's form satisfies all constraints; Implementation II finds it in all six runs. | `klein/model/lwtest48_all.py`, `lwtest48_all.log`; `klein/impl2/control48.py`, `control48.log`, `control48_results.json`; `klein/model/sol48_all.txt`, `verify48_chunk.py`, `v48chunk/`; `klein/model/controls.txt` |
| Test at length 72 with threshold 12: Implementation I with the variables of the levels below 9, 7, 6 and 5 fixed to the values of the quadratic residue code, leaving 3, 9, 15 and 15 free variables. The parametrisation reproduces the code's form exactly. | 7, 338, 25 116 and 25 116 solutions, each set containing the code's form. | `klein/model/lwtest72.py`, output `klein/model/lwtest72.log` (regenerated on 2026-10-23; the counts of the original run are in `klein/model/controls.txt`), `klein/model/control72v4.py` |
| Test at length 80: subtree searches of Implementation II with 6 to 37 free variables below prefixes of the code's form. | Every search finds the form; all solutions verified. | `klein/impl2/control80.py`, `control80b.py`, their logs and result files |
| Test at length 32 with threshold 8: Implementation II against brute force on 15 configurations. | Identical solution sets. | `klein/impl2/test_small.py` |

### Theorems B and C

| Check | Outcome | Files |
|---|---|---|
| Mass of each level of stage (i), against uniform sampling. | Ratios 1.0000, 1.0000, 0.9997 and 1.0000 (10^7 samples per level, standard errors 0.00004, 0.00008, 0.00016 and 0.00041); 10^8 samples give 1.00001 +/- 0.00005 for the third level. | `order3/classification/program1/src/tisample.c`; `order3/classification/program1/regen_20261024/` (`tisample.out`, `tisample_L4_1e8.out`, regenerated on 2026-10-24; commands in `run_tisample.sh`) |
| Mass: the sum of 3/abs(Aut_Mon(E)) over the classes up to monomial equivalence, against the fraction of minimum distance 8 among uniformly random Hermitian self-dual codes of length 24, whose number is given by the mass formula [MOSW78]; the fraction estimated from 2.2 x 10^6 samples of the two programs and from 9 020 000 samples of an independent sampler (order-3 cross-check). | Sum 2.68552 x 10^7; estimates 2.687 x 10^7 +/- 9 x 10^4 and 2.68592 x 10^7 +/- 4.4 x 10^4. | `order3/classification/program1/src/rsd.c`, `program1/samp/`; `order3/cross_check/src/sampler.c`, `scan/samp_*.out`; the sum from the list: `order3/cross_check/rev_lit/scripts/lhs_check.py` |
| Membership: the 23 865 codes of minimum distance 8 among the samples of one sampler, located by class key; the 360 876 of the independent sampler, located by the support invariant, 2 000 of them also by an independent canonical form (the last two: order-3 cross-check). | All in the list. | `order3/classification/program1/src/memb.c`, `program1/samp/`; `order3/cross_check/scan/samp_*.out`, `scan/found2000*`, `src/memb_map.py` |
| Weight enumerators: the values of beta realised in the list. | Exactly the 27 values of [AH23, Prop. 5.3]. | `order3/classification/class_list/beta_hist.txt`; `check_class_list.py` recomputes it from the list |
| Known codes, built from published data, checked (self-orthogonality, rank 12, weight distribution) and located in the list by class key: G24 (x) F4 in three positions, the 25 codes of length 24 in [Har24] and, by exhaustive enumeration, all codes of their form, all double circulant codes, pure and bordered, and the codes C24,4, N24,1, N24,2 of [AH23]. | All found, with abs(Aut_Mon), A8 and self-conjugacy as listed. The form of [Har24] gives 7 + 9 classes, as there; the double circulant codes form 4 classes, as in [GHM07, Table 7]. | `order3/classification/program1/known/` (`kc.c`, `fam.c`, `lookup.sh`, inputs `in_*.txt`, outputs `out_*.txt`, `fam_*.txt`, `look_*.txt`) |
| Both programs at length 16, minimum distance 6, gluing along a word of weight 6. | 4 classes from each, as in [CPS79]. | `order3/classification/program1/cls/n16i.out`; `order3/classification/program2/controls/n16/`, `n16b/`, `t16/` |
| Both programs at length 22, minimum distance 8, with the same double count. | 723 classes up to monomial equivalence from each, as in [HM11], with the distribution of abs(Aut_Mon) of [HM11, Table 3] in all 26 entries; 422 classes up to conjugation. All 898 sampled codes found; the double count gives 602 364 737/12 096 on both sides. | `order3/classification/program1/cls/n22d.*.out`, `n22d.*.log`, `n22count.txt`, `src/clsmiss.c`, `samp/s22_all.txt`; `order3/classification/program2/controls/t22/`; `order3/cross_check/rev_lit/` |
| Canonical keys of random monomial images of a code; the two canonical forms on a common set of codes. | Keys unchanged under the monomial images; the two canonical forms agree on all 5 070 codes compared. | `order3/classification/program1/src/cftest.c`, `cftest2.c`; `order3/classification/program2/c3c/` (the first program's canonical form, used by the second program for the comparison); regenerated on 2026-10-24 in `order3/classification/program2/regen_20261024/` (`run_checks.sh`: a `CFCHECK=1` run of the second program on every 1000th code E_B, 46 in all; the per-E_B counts in `out46.txt.eb` equal those in `program2/full/all.eb`) |
| Full enumeration (4^12 words) of every accepted code, for 8 codes E_B. | All self-orthogonal, of dimension 12 and minimum distance 8, with A8 as listed. | the DEBUGW mode of `order3/classification/program2/src/rglue.c`; regenerated on 2026-10-24 on the codes E_B with ids 0 to 7 (244 accepted codes, no failure): `order3/classification/program2/regen_20261024/` (`run_checks.sh`, `out8.txt`, `out8.txt.eb`); the 8 codes E_B of the original run are not recorded |
| Invariance: the stored class key, abs(Aut_Mon) and self-conjugacy, recomputed under random monomial maps, conjugation and changes of basis on 1 657 codes, among them the two with abs(Aut_Mon) >= 10^5 (order-3 cross-check). | All reproduced. | `order3/cross_check/rev_reclass/cinv.c`, `cinv_*.out` |
| Invariance of the acceptance rule of the first program, on 4 271 codes (order-3 cross-check). | Invariant on all 4 271. | `order3/cross_check/rev_class/src/accinv.c` and its outputs in `order3/cross_check/rev_class/` |
| Reduction: Lemma 4.1 on 2 000 random pairs for the extended quadratic residue code of length 48 with an automorphism of order 3, and the code rebuilt from its two parts. | Lemma holds; the rebuilt code has the original weight distribution. | `order3/reduction/qr48.py` (with `f4lib.py`), output `order3/reduction/qr48.out` (regenerated on 2026-10-24) |
| Reduction, with an independently written Golay code and binary image: for 27 pairs of a code E and a labelled Golay code (random listed codes with random labellings, both classes whose words of weight 8 span 11 dimensions, and G24 (x) F4), the code of length 72 built from each pair and its words of weight 4, 8 and 12 counted directly (order-3 cross-check). | Each code self-dual, doubly even and invariant under sigma, with the numbers of words of weight 4, 8 and 12 that the weight formula gives: three for each violation of (W8), (W10) or (W12). | `order3/cross_check/src/red72.c`, `order3/cross_check/red/red20.out` |
| Normal form (Lemma 4.4): the facts on M24, on the reference code; planted labellings not in normal form (uniformly random bijections), searched for by point placement in 200 codes. | Facts confirmed; the planted code is the unique solution in 200 of 200. | `order3/cross_check/src/m24check.c`; `order3/labelling/point_placement/cross_checks/launch_plantE.sh`, `results/plantE/`, `compare_pz2.py` |
| Reference enumeration: the 995 328 Golay codes that contain a fixed sextet, enumerated as one orbit of S4 wr S6; both programs on seven instances in which every Golay code not containing the sextet, and some random sets, are forbidden, with their solution counts and hash sums of the solution sets compared with the enumeration. | Equal to the enumeration: 31 999, 477, 0, 995 328, 0, 19 312, 9 424. | `order3/labelling/octad_growth/src/gbfs.c`; `order3/labelling/octad_growth/validation/z_*`, `z6.txt`; `order3/labelling/point_placement/cross_checks/z_*`, `zc_*` (the same instances in the compact layout that gbfs reads) |
| Planted Golay codes at forbidden density 0.285, some with forbidden dodecads (60 instances), and 9 further sextet-restricted instances, run by both programs. | One solution per planted instance, the planted code, with identical hashes; identical counts on the 9 instances. | `order3/labelling/point_placement/cross_checks/results/pz/`, `launch_pz.sh`, `launch_gt9.sh`, `compare_pz2.py` |
| Length-48 test: the quadratic residue code of length 48 with an automorphism of order 3 gives a Hermitian self-dual [16,8,6] code and the fixed code e8 + e8. Point placement on the 4 such codes with e8 + e8 and with d16+; in addition, all 9 845 550 labelled doubly-even self-dual [16,8] codes tested against the 4 codes. | Solutions only for the class of the quadratic residue code with e8 + e8: 6 labelled codes, each rebuilt and verified. None with d16+. | `order3/labelling/octad_growth/src/control48/`; `order3/labelling/point_placement/cross_checks/len16/` |
| Common instances of both programs: 1 200 and 200 random codes from the samplers of the two classification programs, 12 codes with beta between 82 and 88, 2 double circulant codes and 4 codes with abs(Aut_Mon) = 6. | Identical decisions; no solution. | `order3/labelling/point_placement/cross_checks/inputs/`, `results/rand1200/`, `results/c3cls200/`, `results/highbeta/`, `results/struct/`, `compare2.py` |
| Symmetry reduction on codes with abs(Aut_Mon) between 6 and 1 728: the whole automorphism orbit of a random Golay code planted, so that the instance stays invariant, and the search run with and without the reduction, two random choices each (order-3 cross-check). | Every run with the reduction finds the solutions. | `order3/cross_check/symt/` (`symtest.out`) |
| Three solvers (the two labelling programs and the independent solver) on 5 sextet instances, against an independent enumeration of the 995 328 Golay codes (order-3 cross-check). | All three match the enumeration. | `order3/cross_check/src/sextet_gt.c`, `order3/cross_check/rev_gtestS/` (`zchk*`), `order3/cross_check/labt/` |
| Planted labellings, not in normal form, searched for by the same three solvers in 6 real codes (among them beta = 157, beta = 133 and a class whose words of weight 8 span 11 dimensions) and in 3 random families (order-3 cross-check). | Each planted labelling found as the only solution. | `order3/cross_check/src/randinst.c`, `src/lab.c`, `order3/cross_check/labt/` |
| Planted Golay codes in real codes: the octad-growth program (the program of the main run, extended to accept planted solutions and run without the symmetry reduction) on the forbidden sets of a [24,12,8] code with the octads and dodecads of a randomly relabelled Golay code G* made allowed, for 8 codes and 2 random choices each. | G* is the unique solution in 16 of 16 runs. | `order3/labelling/octad_growth/validation/q_*.txt`, from a build of `order3/labelling/octad_growth/src/gtestS.c` |

## Lean formalization

The directory `lean/` holds a formal proof in Lean 4 with Mathlib of the deduction of the Main Theorem. The Lean
theorem `C72.mainTheorem_paper` (in `lean/C72T5/Main.lean`) states, in Mathlib's terms, that a binary linear code of
length 72 that equals its dual, has dimension 36, has all weights divisible by 4 and has minimum weight exactly 16 is
mapped to itself by no permutation of the coordinates other than the identity. It has twelve explicit hypotheses.
Nine of them state results from the literature that the paper cites, some in a weaker form, with those of [LP90] and
[MOSW78] combined into one. The other three state the outcomes of the computations: Proposition 2.4 (Theorem A), that
no Hermitian self-dual [24,12,8] code over F4 has a valid Golay code on its coordinates (Theorems B and C), and that
no code Y_k has a solution (Theorem D). `lean/README.md` states the twelve hypotheses and gives, for each statement of
the paper, the Lean theorem that proves it or the hypothesis through which it enters.

The rest of the deduction is proved in Lean: the decompositions under automorphisms of prime order, the reductions to
the three computations and the final step, and also Lemma 2.5, Lemma 4.4 with the facts about M24 that it needs,
Lemma 6.3 with both symmetry tests, and the reduction of Proposition 3.7 from codes to instances. Lean checks neither
the cited results nor the computations, and `lean/README.md` also lists the steps of the paper that are not
formalized.

Lean `leanprover/lean4:v4.35.0-rc3` and Mathlib at commit `c55e6e786f49471c72fbddbec5415808896aec1e` are pinned in
`lean/lean-toolchain` and `lean/lake-manifest.json`. With elan installed, run in `lean/`:

    lake exe cache get
    lake build C72T1 Paper C72T2 C72T3 C72T4 C72T5 C72T5W C72T6 C72T6D C72T6K C72T6O3 C72T6O5 C72T5Controls.HD48Axioms

The first command downloads the compiled Mathlib, which with its dependencies takes about 7 GB of disk space. The
second compiles the 102 modules of the formalization, in about nine minutes on one core. After the build,
`./check_controls.sh` checks that each of the 53 control modules, which state something false, fails with the error
recorded in `controls_expected.txt`, and that the checker rejects the 34 wrong entries of `plants_expected.txt`. Its
output ends with `controls: 53 of 53 pass` and `plants: 34 of 34 rejected`.

`lean/AXIOMS_ALL.txt` collects the output of `#print axioms` for the 638 theorems named in the 13 axiom-report
modules. Each of them depends on at most `propext`, `Classical.choice` and `Quot.sound`, the standard axioms of Lean.
No module uses `sorry`, declares an axiom or calls `native_decide`.

## Provenance of the files and records

Paths below are given as in the section of each result.

### Editing for publication

We copied the files from the project directories with three kinds of change, all listed in `REDACTIONS.tsv`. We
replaced absolute paths in programs by paths relative to the program or by arguments, without changing what the
programs compute; in records, home directories, account names and machine names by the labels of "Conventions in the
records"; and we removed a few working notes inside records (for example, who asked for a check). Files and
directories whose names contained a machine name received the same labels, and a few directories and files were
renamed to match the terms of the paper (main run, independent implementation, cross-check). After these changes we
rebuilt the programs from the files of this archive and ran them on small cases; the outputs agreed with the shipped
records. Records that list sha256 values (manifests, coverage files) give the sha256 of the original files. Working
notes and reports written during the project are not included. We regenerated the outputs whose original records
were not kept, on 2026-10-23 and 2026-10-24, with the shipped programs; the sections of the five results mark each of
them as regenerated, with the date. They also give the commands, name the few scripts that were not rerun or whose
output was not kept, and report what the working notes say about the files.

### Files left out, and how to regenerate them

#### Theorem A

- The complete node dump of the rerun of job (6,1) (13 254 989 nodes, 103.8 MB compressed; sha256 of the
  uncompressed file 701c6ff2461338d552027b304a63a2906dc014d6ccc6082da484520c77963f08), because of its size;
  `cross_check/runs/chainD.sh` regenerates it with `gen4dump2` (see the order-5 cross-check in "Checks of Theorem A").
- Tar copies of the log directories that are shipped here as plain files (they are byte-identical), and the archive of
  the re-check runs, whose files are shipped here except compiled binaries, copies of the search sources, marker files
  and empty outputs.
- The specification written for the independent implementation, which also gave operational details. Its
  mathematical content is the statement of Proposition 2.4 with the definitions of Sec. 2.3, and a list of symmetries
  that could be used in the implementation once it was proved that they preserve the condition. We also leave out
  the report that came with the independent implementation; `py/stats.py` reads its numbers from the run logs.
- The original output of the check of the independent implementation's eight five-row nodes was not kept.
  We regenerated `five_row_nodes/check6_indep_depth5.out` on 2026-10-23 with the shipped `check6.py`; it contains no
  timing field.

#### Proposition 3.8

- The run binary of Implementation I (its sha256, beginning 0be528e5, is recorded in `MANIFEST_lwe.txt`); build it
  from `impl1_runs/lwe.c` as described under "Building and rerunning" of Proposition 3.8.
- `invs.pkl`, `classes.pkl` and the per-instance parameter pickles (`lwf_*.txt.pkl`, `map_*.pkl`): regenerate with
  `model/autinv.py`, `model/classes.py` and `model/lwprep.py` (the checks in `checks/impl1/scripts/indep_check.py`
  write their own maps).
- The raw files of the planted and pinned tests of the third solver (`checks/gd/planted/`, `pinned/`,
  `plantedfull/`; about 300 MB): regenerate with `checks/gd/scripts/run_planted.sh` and `run_pinned.sh`; the logs
  and summaries are included. Likewise the instance files regenerated in the cross-check of Implementation I
  (their hashes are in `box_regen_sha.txt`), and its copies of the run outputs (identical to `impl1_runs/out*`).
- The partial runs of the third solver on the six instances with the largest trees (sub-split jobs and runs with a
  symmetry reduction, built from later versions of the program). The paper does not use them.
- Run directories of these tests on the machine that ran them, and the instance copies there, which are identical to the
  shipped instance files (checked by sha256).

#### Theorem C

- The per-slice outputs of stage (ii) of the first program (288 files): merged into the class list.
- The 69 449 lines of the list with AUT > 3, which the octad-growth program reads for its symmetry reduction
  (cls24_aut_gt3.txt, sha256 9eb40d94054726e5889e743df70a3d35aa0e30b8ba2d8a237ea11715398db4e2):
  `zcat class_list/cls24.txt.gz | awk '$2 > 3'` reproduces the file byte for byte.
- The accepted codes of the second program (13 891 590 lines, about 1 GB compressed, files c_XXXX.txt.gz):
  regenerated by rglue over full/E_B_L5.txt; full/all.eb keeps the per-E_B summary lines and full/compare_report.txt
  the comparison.
- The raw level-5 outputs of the second program (n24/raw*_*.txt, 1.4 GB): regenerated by ebcls2 at level 5;
  n24/L5.txt is their deduplicated result.
- The binary arrays of the 64-bit invariant per class (cross_check/scan/full_*.inv, 108 MB) and their sorted
  copy: written again by src/cscan.c over the class list (six shards); the summary counts are in the .hist and .log
  files. The array of A8 per class (cov/A8.u16) is derived from the list by src/mkA8.py.
- The input slices cross_check/scan/nd_part_00..07 (they are the lines of scan/nd_all.txt).
- Development versions of the programs, the nauty sources, copies of published papers, and the
  scripts that collected outputs from the machines over the network.
- The checks of known/ that concern codes with an automorphism of order 3 (ord3*, ordr*, cert*), which the paper
  does not use.

#### Theorem B

- The parts of the class list given to the point-placement machines (about 1.5 GB of slices of the class list): their
  sha256 are in `point_placement/main_run/shares/`; each part is regenerated from the class list with the command
  under "The main runs" of Theorem B.
- `planted_control_pkg.tgz` (sha256 02d496ad...) and the archive of the octad-growth result files `res_all.tgz`
  (sha256 d98ad864...): the same files are shipped unpacked in `point_placement/planted_control/` and
  `octad_growth/main_run/results/`.
- The monitoring and remote-management scripts of the main-run machines, and two partial octad-growth runs that were
  stopped and are not part of the coverage (a redundant run of 220 slices and a local block of indices from 13 000 000).
- Development versions of both programs that produced no result cited in the paper.

#### Theorem D

Of the executables of the eight runs made outside the package fleet, two are in `engines/`: lwe8
(`lwe8_reference/lwe8`), which ran Y8, and lwe11b (`b/lwe11b`), which ran the parts of Y29 after the switch. The
others are not included in this archive: the native builds of lwe8, lwe10 and lwe11 made on the machines of the runs,
the portable builds of lwe10 and lwe11 used for some parts of Y1 and Y4, and the build of lwe5 used for Y39. Their
sha256 are in the runs' records (for the portable builds also in `engines/explore/frozen3/BUILD.sha256` and
`frozen4/BUILD.sha256`), except for lwe5. The sources are in `engines/explore/` (lwe5 also in `runs/y39/inputs/src/`),
and the build scripts of lwe8, lwe10 and lwe11 in `engines/lwe8_reference/`, `engines/explore/frozen3/` and
`frozen4/`. Their outputs are covered by the cross-check reruns with the reference program and, for Y8, Y22, Y23 and
Y39, by the independent re-searches.

We shipped every file of the source directories except the following; `order2/DROPPED.tsv` lists each of them with its
reason:
- compiled binaries: copies of the executables of the main runs (those are under `engines/`), other builds of
  the shipped sources, and the portable executables of lwe10 and lwe11 used for some parts of Y1 and Y4 (see above);
- copies of package inputs, executables and box kits kept in the cross-check directories, and a second copy of
  `engines/explore/frozen3/`; the packages are under `packages/`;
- scratch directories, caches and Python bytecode;
- scripts that reach machines over ssh, stop tasks on a machine, or read the project's messaging, and two
  aggregation scripts of the working directories, whose outputs (`summary/RUN_SUMMARY.txt`) are shipped;
- superseded versions of checkers and coverage reports, and two narrative texts whose content this README covers;
- a note among the part logs of Y1 on stopping its helper run on the local machine; `runs/y1b/RUN_SUMMARY.txt`
  records the 15 stopped parts and their recomputation.

### Changed files, and checksums cited in the paper and its records

#### Theorem A

Twenty scripts differ from the files that were run: we replaced absolute paths to the project directories by
paths relative to the script, and removed the first step of `logs/main_run/collect.sh`, which copied the log
directories from the two machines. No computation changed. The two machines appear as hostA and hostB in directory names. Three build scripts (`build.sh`) and
`five_row_nodes/check6_indep_depth5.out` are new. All other files are byte-identical to the files of the original
runs.

#### Proposition 3.8

| Item | sha256 | In this supplement |
|---|---|---|
| Run source of Implementation I | 8c03fe1842eb5d1f0c8a4379c4f4a2f804df7871e93fd1d5dd95ae033acdfc1d | `impl1_runs/lwe.c`, unchanged |
| Run binary of Implementation I | 0be528e52d08429cdfaec52cb51c3f4d0affdd9a558d08076c9e717e1bb9ed74 | not shipped; listed in `MANIFEST_lwe.txt` |
| Later source with the PROBE mode | 5b6c344bdb0709079f045d8dbef1a8542a7441e88611334116009e6251784a93 | `model/lwe.c`, unchanged |
| Instance generator `lwprep.py` | 53900c0bf18785dfd7727d8bbbcc82c8a21e19832f4fa9cc4ce01b6665ea3022 | `model/lwprep.py`, two path lines edited (REDACTIONS.tsv) |
| `MANIFEST_lwe.txt` | 54d05fba08638eac8cdb4449cd2188e54a4e73d23b31f2e268420c2d842ed48b | header comment lines edited, hash lines unchanged (REDACTIONS.tsv) |
| Totals record of the runs (here `impl1_runs/totals.txt`) | 02dbab4dd8e23174ed617e7ec8caa58ec15aba6bd8bb44ed859e59a1276c1972 | edited (REDACTIONS.tsv) |
| `controls.txt` | 2692a0a95601b3b21a6afaf0f76dc9c4805eb79a906ae541b30fd1dc9581cf67 | `model/controls.txt`, edited (REDACTIONS.tsv) |
| `lwtest48_all.py` as run | 7387340031536752b960b3e3185643f472cf5fd07a2b31b186d93bdcf4570605 | `model/lwtest48_all.py.as_run`, home path replaced (REDACTIONS.tsv) |
| `lwtest48_all.log` | 83383d4b58a1a7537b6dfcd6cab14b51fbd4e5cc143b3423ce2193cbc01ec456 | `model/lwtest48_all.log`, unchanged |
| `sol48_all.txt` | 4be78caf546d47a040f68f2be427fa96318f5ef09cf47f3828e3fb2850f3cb7d | `model/sol48_all.txt`, unchanged |
| The 41 codes | c322bf970b7ba24be65b79b923892567fa0539ebabb0bb2679a6a2c2f7aa71b9 | `codes36.txt`, unchanged |
| Archive of the run directories | 61fb8362eb130cae43717a5308f6d07738bf63ec7fceb727a8702e113abd07ce | not shipped; its outputs, run sources and scripts are in `impl1_runs/` and `gd_runs/` (byte-identical before redaction) |
| Inputs pushed for the six split runs | aa1cf4bbc488b6a9200fcbd2a57efeddf948a5599dce9e29de6fe0b59064acb8 | not shipped; its `lwe.c` is the run source above and its seven instance files equal the shipped ones |

#### Theorem C

| Item | sha256 | Status in this supplement |
|---|---|---|
| decompressed class list | 58137da319c7...a805e | recomputed by check_class_list.py from class_list/cls24.txt.gz |
| class_list/cls24.txt.gz | 6569bde3a4d7...0f37 | file as produced |
| class_list/beta_hist.txt | 1548f6c16b0f...6077 | identical copy |
| class_list/aut_hist.txt | 8cd12b971496...97ee | identical copy |
| sorted extracts of both lists | 1370e6023a7d...2258 | recomputed from the list (see "Second classification program") |
| checksum list of the second program's run | 077ec498eb5d... | program2/full/frozen_SHA256SUMS.txt, identical |
| source of the main-run octad-growth executable | 5a198e1f32fd... | cross_check/gth/gtestS_prod.c and rev_gtestS/gtestS_prod.c, identical copies |

The file program2/src/compare_full.sh differs from the file that was run (we replaced one path); its original
sha256 is the one listed in program2/full/frozen_SHA256SUMS.txt and in REDACTIONS.tsv.

#### Theorem B

The following files are shipped unchanged (sha256 of the shipped file): `octad_growth/src/gtestS_prod.c`
5a198e1f32fded3fe4d90cbd8560ddff519c02ef4edc60dfb41b761d97eaff61; `octad_growth/src/gtestS.c` c8781b4f...;
`octad_growth/src/gtest4.c` c4e58772...; `octad_growth/src/gtest9.c` 6f9feb1f...; `point_placement/src/csp5p.c`
d5d9cdf59350a65b86deee2a8dfa9ee341e1dd28ad9fabe3831678bcbdfa3258; `point_placement/main_run/strict_check.py`
591525d4...; `point_placement/main_run/results/aggregate_final.txt` 6b803da1...;
`octad_growth/validation/rank11_prod_nosym.out` f2313f49...; `octad_growth/rank11/rank11_gtestS.out` 271c70e8...;
`octad_growth/rank11/rank11.txt` 6da12c34...; `octad_growth/validation/symchk.out` 75a42764....
We redacted the following records (host names and home paths replaced, role names removed), so their sha256 differ
from the cited values, which are the sha256 of the original files; `REDACTIONS.tsv` lists both: `COVERAGE_PROOF.txt` 6429c93f..., `octad_growth/main_run/MANIFEST.txt` 41fc25b8...,
`PROVENANCE.txt` 95aba19d..., `COVERAGE.txt` 0fe54971..., `covmanifest.py` 24939382..., `FINAL_MANIFEST.txt`
c3edcf90..., `self_tests/SUMMARY_mid.txt` e8906e4c..., `self_tests/SUMMARY_final.txt` 03039ab9....
We repacked the three result archives with neutral owner fields; their members are byte-identical to the originals
(sha256 of the original archives f34bc7ab..., 40a8325a..., 69bf0a49...; members listed in `members_host*.sha256`).

### Box-check records of Theorem D

- The six single-machine runs (Y1, Y4, Y5, Y8, Y22, Y23): their box-check scripts are `check_box.sh` in
  `engines/lwe8_reference/` (lwe8) and in `engines/explore/frozen3/` and `frozen4/` (lwe10 and lwe11). They verify the
  input and source hashes against `INPUTS.sha256` and compare the probe estimate with `PLAN.txt`; the scripts of lwe10
  and lwe11 also run part 17 of 200 000 with lwe8 and with the build and compare the outputs. The check logs were not kept; only
  result lines survive, in `RUN_SUMMARY.txt` and `RUN_LOCAL.txt`. They record the input hashes and the reproduced probe
  estimate, except for three checks of Y1 that are recorded only as passed: those of its lwe11 build on hostB and hostC,
  the two machines that ran most of its parts, and that of the portable lwe11 build on the local machine. Four
  executables were built from sources other than lwe8: the native lwe11 build, with the same sha256 on hostB and hostC
  (Y5 on hostC, Y1 on both), the native lwe10 build (Y23 on hostB), and the portable lwe10 and lwe11 builds (some parts of Y1 and Y4 on the local
  machine). For each of them a result line records identical output with lwe8 on one part, on the inputs of Y5, Y23, Y1
  and Y4 respectively. Y8, Y22 and the parts of Y4 on hostC ran builds of lwe8. The 13 reruns of whole parts in
  `cross_check/coverage/xnat/` include parts from every executable and machine of these runs, among them the parts of
  Y1 from hostB and hostC.
- Y29: its two machines, hostK and hostL, each ran the full check for both program versions, lwe10 and
  lwe11b. Three of the four check logs are in `runs/y29/checks/` (hostK with lwe10, hostL with lwe10 and with lwe11b).
  The log of the check of lwe11b on hostK was not kept; line 9 of `RUN_SUMMARY.txt` records its
  result. `hostL_driver_and_build_logs.txt` in the same directory holds driver and build lines of hostL,
  not a check.
- The 2 632 parts of Y12 produced on fleet57 count through that machine's check, which passed on 2026-10-27, after the run was complete; they also have identical second runs on checked machines.

## Versions

Paper: doi:10.5281/zenodo.23789973 (all versions: doi:10.5281/zenodo.23603743). This supplement:
doi:10.5281/zenodo.23789974 (all versions: doi:10.5281/zenodo.23603745). Version 1 (doi:10.5281/zenodo.23603746)
contains the files for Theorems A, B and C and Proposition 3.8; version 2 keeps them unchanged and adds the directory
`order2/` for Theorem D and the directory `lean/` with the Lean formalization. This file, `README_v2.md`, describes
both versions. Version 1 and its `README.md` use the letters of the first version of the paper:

| Version 1 | This file | Result |
|---|---|---|
| Theorem A | Theorem A | no automorphism of order 5 |
| Theorem B | Proposition 3.8 | no subgroup C2 x C2 |
| Theorem C | Theorem B | no automorphism of order 3 |
| Theorem D | Theorem C | the classification of the Hermitian self-dual [24,12,8] codes |
| - | Theorem D | no fixed-point-free involution (new in version 2) |
