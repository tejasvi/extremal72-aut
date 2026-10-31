# Programs for "The automorphism group of an extremal [72,36,16] code is trivial"

This repository holds the programs for the paper

> Tejasvi Singh Tomar, *The automorphism group of an extremal [72,36,16] code is trivial*, Zenodo, 2026.
> https://doi.org/10.5281/zenodo.23789973

which proves that a binary doubly-even self-dual [72,36,16] code has no automorphism other than the identity. By
earlier work, the automorphism group of such a code is trivial or isomorphic to C2, C3, C2 x C2 or C5 (M. Borello,
Contemp. Math. 632, 2015, Thm. 6.3), and every involution of such a code is fixed-point-free (S. Bouyuklieva, Des.
Codes Cryptogr. 25, 2002). The paper excludes the four groups by computer searches:

| Directory | Result in the paper | Main computation | Checked by |
|---|---|---|---|
| `order5/` | Theorem A: no automorphism of order 5 | a search over 7 x 7 unitary matrices over F16, in 224 jobs of 8 threads | a second implementation of the search |
| `order3/labelling/` | Theorem B: no automorphism of order 3 | a search over the labellings of the Hermitian self-dual [24,12,8] codes over F4 by the extended Golay code, one class of codes at a time | a second implementation, run on every class |
| `order3/classification/` | Theorem C: there are 26 924 931 Hermitian self-dual [24,12,8] codes over F4 up to monomial equivalence, and 13 485 816 up to monomial equivalence and conjugation | a classification program | a second classification program and a double count |
| `order2/` | Theorem D: no fixed-point-free involution | 41 searches over symmetric bilinear forms, one for each self-dual [36,18,8] code | partial reruns and a coverage check for all 41 searches; a separately written program for five of them (Y8, Y18, Y22, Y23 and Y39) |
| `klein/` | Proposition 3.8: no subgroup C2 x C2, a much smaller check of a case that Theorem D also excludes | a search over 119 instances | a second implementation, and a third solver on the 113 instances other than the six with the largest search trees |

The programs are written in C and Python 3. Building and running them needs a C compiler (with OpenMP for the order-5
search), Python 3 (some scripts also use numpy, two use python-flint), nauty 2.9.3 and, for one program, zlib. The section
"Running times" of `README_v2.md` gives the computing time of each main run except that of Theorem C.

The directory `lean/` holds a Lean 4 formalization that proves the Main Theorem from twelve hypotheses: nine of them
state published results that the paper cites, some in a weaker form, and three state the outcomes of the paper's
computations. Its `README.md` lists the hypotheses and explains how to build the project and check its controls.

## Data and records

The supplement is archived on Zenodo, https://doi.org/10.5281/zenodo.23789974. It holds the instances, logs, results
and certificates from the runs, and 21 of the executables used in the main runs for Theorem D. Its twelve files (2.7 GB)
are also attached to release v2 of this repository. Version 1 of the supplement covered Theorems A to C and
Proposition 3.8; version 2 adds the directories `order2/` for Theorem D and `lean/` for the Lean formalization and
keeps the top directory name `extremal72-aut-supplement-v1/`. The program files and the Lean files here are copies of
those in the supplement, at the same paths below that directory.

To check the downloaded files and unpack them, run in the directory that holds all twelve:

    sha256sum -c SHA256SUMS
    for f in extremal72-aut-supplement-v*.tar*; do tar -xf "$f"; done
    cd extremal72-aut-supplement-v1 && sha256sum -c SHA256SUMS && (cd order2 && sha256sum -c SHA256SUMS) &&
      (cd lean && sha256sum -c SHA256SUMS)

`README_v2.md`, copied here unchanged, is the README of the supplement. Its table "Where to start" lists, for each
result, the main run, the checks made on it and one command, run in `extremal72-aut-supplement-v1/`, that re-derives
the totals from the records. Each result then has its own section, with the build and run commands (for Theorem D, those of its checks), the expected output
and all its checks. Where `README_v2.md` mentions other files, such as the version 1 `README.md`, `SHA256SUMS` or the
instance, log and result files, it refers to the files in the supplement.

## Licence

The program files are licensed under the Apache License 2.0 (`LICENSE`). The documentation and the data are licensed
under CC BY 4.0 (`LICENSE-DATA`).

## Citation

Please cite the paper above. To cite the programs or the data, cite the supplement:

> Tejasvi Singh Tomar, *Programs, data and certificates for: The automorphism group of an extremal [72,36,16] code is trivial*, Zenodo, 2026.
> https://doi.org/10.5281/zenodo.23789974
