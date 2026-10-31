# Lean formalization for "The automorphism group of an extremal [72,36,16] code is trivial"

This directory holds a Lean 4 formalization for the paper

> Tejasvi Singh Tomar, *The automorphism group of an extremal [72,36,16] code is trivial*.

The paper proves that a binary doubly-even self-dual [72,36,16] code has no automorphism other than the identity. The
Lean files prove this Main Theorem from twelve hypotheses. Nine of them state published results that the paper cites,
some in a weaker form, and three state the outcomes of the paper's computations. Each hypothesis is a definition of
type `Prop` and an explicit premise of the theorem, except that the twelfth, `T4.H_D`, is a family `Fin 41 → Prop`
and the theorem assumes `T4.H_D k` for every k. The rest of the argument is proved in Lean, and the kernel checks it
with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.

## The theorem

In words, the theorem `C72.mainTheorem_paper` in `C72T5/Main.lean` says the following. Assume the twelve hypotheses
listed below. Let C be a subspace of F₂⁷² that is equal to its dual, has dimension 36 and has all weights divisible
by 4, whose nonzero words have weight at least 16, and which contains a word of weight 16. Then the identity is the
only permutation p of the 72 coordinates with Cp = C.

Here a permutation p moves the entry of a word at coordinate i to coordinate p(i), as in the paper. The statement
uses Mathlib's own notions (`Submodule (ZMod 2) (Fin 72 → ZMod 2)`, the dot product, `Module.finrank` and
`hammingNorm`). These definitions are in `C72T1/Paper.lean`, together with proofs that they agree with the project's
`Ext72` and `Aut`. The theorem `C72.mainTheorem` states the same result with `Ext72` and `Aut`.

No extremal [72,36,16] code is known. If none exists, the theorem holds trivially, and so do the five hypotheses that
are statements about such codes (`hyps_of_no_extremal` in `C72T5/Known.lean`).

`C72.mainTheorem_weaker` in `C72T5W/MainWeaker.lean` proves the theorem with a weaker form of hypothesis 3. It
assumes only that the contracted fixed code is self-dual and has a word of weight 8, and it proves from the
hypotheses on C that this code has minimum weight at least 8.

## The twelve hypotheses

1. `H_primes`: every prime that divides the order of Aut(C) is 2, 3 or 5. This follows from Borello's list of the
   possible automorphism groups (M. Borello, 2015, Thm. 6.3).
2. `H_L1`: every involution in Aut(C) is fixed-point-free (S. Bouyuklieva, 2002).
3. `T4.H_L2`: the contracted fixed code of a fixed-point-free involution in Aut(C) is a self-dual [36,18,8] code
   (G. Nebe, 2012, Thm. 3.1).
4. `T4.H_L3`: every self-dual [36,18,8] code is equivalent to one of 41 codes Y₀, …, Y₄₀ (C. Aguilar Melchor and
   P. Gaborit, 2008; M. Harada and A. Munemasa, 2012).
5. `H_CP5`: an automorphism of order 5 has exactly two fixed points (J. H. Conway and V. Pless, 1982).
6. `H_CP3`: an automorphism of order 3 has no fixed point (Conway and Pless, 1982; Bouyuklieva, 2004).
7. `H_16`: every doubly-even self-dual code of length 16 is equivalent to e₈ ⊕ e₈ or to d₁₆⁺ (E. M. Rains and
   N. J. A. Sloane, 1998).
8. `H_Golay`: every doubly-even self-dual code of length 24 with minimum weight at least 8 is equivalent to the
   extended Golay code (the uniqueness of the extended Golay code, which the paper uses through T. Feulner and
   G. Nebe, 2012, Lemma 3.1).
9. `H_LP`: every Hermitian self-dual code of length 24 over F₄ with minimum weight at least 8 has a word of weight 8.
   This follows from the bound d ≤ 10 of F. J. MacWilliams, A. M. Odlyzko, N. J. A. Sloane and H. N. Ward (1978) and
   from the theorem of C. W. H. Lam and V. Pless (1990) that no Hermitian self-dual [24,12,10] code exists.
10. `H_A`, Proposition 2.4 (the order-5 search): no 7 × 7 matrix U over F₁₆ with UU* = I
    satisfies M(a) + M(aU) ≥ 16 for every nonzero a, where M is the weight function of Section 2.
11. `H_CB`, Theorem C together with the labelling search of Theorem B (order 3): no Hermitian self-dual [24,12,8]
    code over F₄ has a valid labelling of its coordinates by the points of the extended Golay code (Section 4).
12. `T4.H_D k` for k = 0, …, 40, the 41 searches of Theorem D (order 2): for every form B in A₀(Y_k), some word of
    Y_k of weight 8, 10 or 12 has a bad syndrome (Section 6).

The docstring of each definition gives the exact statement and its source. `C72T5/Main.lean` restates all twelve
with `Iff.rfl`, so that they can be read in one place.

## What is not formalized

- The twelve hypotheses, that is, the cited results and the three computations.
- The search programs themselves. The theorem `H_D_of_search` in `C72T6D/Bridge.lean` derives `T4.H_D k` from three
  facts about the order-2 search, which are premises of that theorem: the words that give the syndromes of the key
  words are disjoint from them (`hdisj`), a node is removed only under the condition of Lemma 6.3 (`hrem`), and the
  search reports no solution (`hnone`). In the same way, the instances of the
  Klein-group case in `C72T6K` are parameters.
- Theorem C (the counts of the classification), the converse direction of Lemma 2.2 (Theorem A uses only the forward
  direction), Lemma 6.1 (a), the uniqueness of B in Lemma 3.2 and the part of Lemma 3.5 about codes.
- The minimum weight 8 of the 41 codes Y_k and their pairwise inequivalence. The supplementary archive checks both by
  computer.
- The bound d ≤ 16 for doubly-even self-dual codes of length 72. The converse statements of Propositions 3.7 and 6.2
  conclude minimum weight at least 16 instead of minimum weight 16, and they assume that Y_k has minimum weight at
  least 8.
- The bound d ≤ 8 for self-dual codes of length 36. The weaker hypothesis of `C72.mainTheorem_weaker` includes the
  word of weight 8.

## Paper statements and Lean names

| Paper | Lean | File | Status |
|---|---|---|---|
| Main Theorem | `C72.mainTheorem`, `C72.mainTheorem_paper` | `C72T5/Main.lean` | from the twelve hypotheses |
| Final deduction (Cauchy's theorem) | `main_of_cited`, `paperMain_of_cited` | `C72T1/Final.lean`, `C72T1/Paper.lean` | proved |
| Decomposition under an automorphism of odd prime order | `decomposition`, `contracted_selfDual`, `exists_relabel` | `C72T1/Decomp.lean`, `C72T1/Labelling.lean` | proved |
| Section 2.1 (F₁₆, ψ, C₀, C₁) | `selfDual_C0`, `C1_hSelfDual`, `wt_phi0` | `C72T3/Decomp5.lean`, `C72T3/Lemma21.lean` | proved |
| Lemma 2.1 | `lemma21` | `C72T3/Lemma21.lean` | from `H_16` |
| Lemma 2.2 (forward direction) | `lemma22` | `C72T3/Lemma22.lean` | proved |
| Lemma 2.3 | `lemma23` | `C72T3/L23.lean` | proved |
| Proposition 2.4 | `H_A` | `C72T3/Hyp.lean` | hypothesis |
| Lemma 2.5 | `lemma25`, `lemma25_sol`, `normalise_joining`, `H_A_iff_nf` | `C72T6O5/Normal.lean`, `C72T6O5/Scan.lean` | proved |
| Theorem A | `thmA_of_hyps` | `C72T3/ThmA.lean` | from `H_CP5`, `H_16`, `H_A` |
| Definition 3.1 | `CB` | `C72T4/Model.lean` | definition |
| Lemma 3.2 | `model` | `C72T4/Lemma32.lean` | existence proved, uniqueness of B not formalized |
| Lemma 3.3 (a) | `wt_pv_add` | `C72T4/Model.lean` | proved |
| Lemma 3.3 (b), (c) | `model`; `CB_selfDual`, `CB_doublyEven`; `diag_of_span` | `C72T4/Lemma32.lean`, `C72T6/Converse.lean`, `C72T6D/Basis.lean` | proved |
| Lemma 3.3 (d) | `aStd_mem_CB`, `Yof_CB` | `C72T6/Converse.lean` | proved |
| Lemma 3.4 | `pair_form`, `pair_form_props`, `pair_form_fpf`, `mem_Aut_Yof_of_pair_form`, `exists_swapP`, `swapP_conj`, `Yof_map_swapP`, `liftP_mem_Aut_CB_iff` | `C72T6K/Klein.lean`, `C72T6K/Additions.lean` | proved |
| Lemma 3.5 | `InA0_add`, `G0_symm`, `G0_diag`; `formAct_DT_of_invariant`, `formAct_DT_of_transversal`, `formAct_of_mem_GK`, `InA_add` | `C72T6/Gauge.lean`, `C72T6K/Klein.lean` | proved for forms |
| Lemma 3.6 | `lemma36`, `lemma36_iff` | `C72T4/Lemma36.lean`, `C72T6/Solutions.lean` | proved |
| Proposition 3.7 | `prop37_forward`, `prop37_forward_slice`, `prop37_forward_reps`, `prop37_converse`, `prop37_converse_E`, `ruledOut_iff_prog` | `C72T6K/Prop37.lean`, `C72T6K/Additions.lean`, `C72T6K/Weight14.lean` | proved |
| Proposition 3.8 | `prop38_of_searches`, `prop38_subgroup` | `C72T6K/Prop37.lean`, `C72T6K/Additions.lean` | from the searches (not used by the Main Theorem) |
| Lemma 4.1 | `lemma41` | `C72T2/Coords.lean` | proved |
| Lemma 4.2 | `lemma42` | `C72T2/Lemma42.lean` | proved |
| Proposition 4.3 | `prop43_forward`, `prop43_converse`, `prop43`, `exists_validGolay_iff` | `C72T2/TheoremB.lean`, `C72T6O3/Prop43.lean` | proved |
| Lemma 4.4 | `lemma44`, `lemma44_general` | `C72T6O3/Lemma44.lean`, `C72T6O3/Lemma44General.lean` | proved |
| Theorem B | `thmB_of` | `C72T2/TheoremB.lean` | from `H_CP3`, `H_Golay`, `H_LP`, `H_CB` |
| Theorem C | | | not formalized (enters through `H_CB`) |
| Lemma 6.1 (a) | | | not formalized |
| Lemma 6.1 (b) | `G0_apply_disjoint`, `syn_add`, `slice_existsUnique`, `slice_A0_existsUnique` | `C72T6/Gauge.lean`, `C72T6/Search.lean`, `C72T6/Slice.lean` | proved |
| Proposition 6.2 | `prop62_forward`, `prop62_forward_slice`, `prop62_converse`, `prop62_converse_E`, `prop62_converse_fin72` | `C72T6/Solutions.lean`, `C72T6/Converse.lean`, `C72T6D/Fin72.lean` | proved |
| Lemma 6.3 and the pruning tests | `lemma63_abstract`, `lemma63_order2`, `lemma63_key`, `first_test`, `coset_rule`, `coset_rule_table`, `second_test` | `C72T6/Search.lean`, `C72T6D/CosetTable.lean` | proved |
| From the search to `H_D k` | `H_D_of_search`, `thmD_of_search` | `C72T6D/Bridge.lean` | from three premises about the search |
| Theorem D | `thmD_of_HD` | `C72T4/Main.lean` | from `T4.H_D k` |
| No fixed-point-free involution | `noFPFInv_of`, `noFPFInv_of'` | `C72T4/Main.lean`, `C72T5W/MainWeaker.lean` | from `H_L2` (or its weaker form), `H_L3`, `H_D` |
| Checks on known codes | `known_codes`, `A0_nonempty`, `not_H_CB48`, `not_H_D48` | `C72T5/Known.lean`, `C72T5/CB48.lean`, `C72T5Controls/HD48.lean` | proved |

## Layout

| Library | Contents |
|---|---|
| `C72T1` | codes, duals, weights and the automorphism group; the decomposition under an automorphism of odd prime order; the labelling lemma; the final deduction; the statements in Mathlib's terms (`C72T1/Paper.lean`) |
| `C72T2` | automorphisms of order 3 (Section 4, Theorem B) |
| `C72T3` | automorphisms of order 5 (Section 2, Theorem A) |
| `C72T4` | fixed-point-free involutions (Sections 3 and 6, Theorem D) and the 41 codes Y_k |
| `C72T5` | the Main Theorem from the twelve hypotheses, and checks of the definitions on known codes |
| `C72T5W` | the Main Theorem with the weaker form of hypothesis 3 |
| `C72T6` | order 2: Lemma 6.1 (b), the slice property, Lemma 6.3, Proposition 6.2 |
| `C72T6D` | order 2: from the search to `H_D k`, the table of the coset rule, Lemma 3.3 (c) on a basis, Proposition 6.2 on `Fin 72` |
| `C72T6K` | Klein four-groups: Lemmas 3.4 and 3.5, Propositions 3.7 and 3.8 |
| `C72T6O3` | order 3: Lemma 4.4 and the converse of Proposition 4.3 |
| `C72T6O5` | order 5: Lemma 2.5 |

The comments refer to these libraries as T1, …, T6O5. The libraries `C72T1Controls`, …, `C72T6O5Controls` hold the
must-fail controls, and `C72T1Plants` and the modules `P01`–`P05` of some control libraries hold the plants (see
below). `C72T5Controls` also holds three modules that do build, `HD48Check`, `HD48` and `HD48Axioms`; they prove that
the analog of `H_D` for a code of length 48 is false.

Some modules hold data computed from files of the supplementary archive. `C72T4/Codes36Data.lean` holds the 41 codes
Y_k from `order2/codes/codes36.txt`. `C72T2/OctDodData.lean` holds the octads and dodecads of the Golay code from
`octdod.txt` of the labelling programs, and `C72T6O3/M24Data.lean` holds automorphisms of the Golay code computed from
the same octads. `C72T5/CB48Data.lean` and `C72T5/CB48Rows.lean` come from `control48/qr48_DE.txt`. The header of
each of these modules names its source file.

## Building

Install Lean through elan. The file `lean-toolchain` selects Lean `v4.35.0-rc3`, and `lake-manifest.json` pins
Mathlib at the tag `v4.35.0-rc3` (commit `c55e6e786f49471c72fbddbec5415808896aec1e`). In this directory, run

```
lake exe cache get
lake build C72T1 Paper C72T2 C72T3 C72T4 C72T5 C72T5W C72T6 C72T6D C72T6K C72T6O3 C72T6O5 C72T5Controls.HD48Axioms
```

The first command downloads the compiled Mathlib, and the second compiles the 102 modules of this project. On one
core this takes about nine minutes. Do not build the control libraries as a whole, since their modules are meant to
fail.

## Checking the controls

Each control module states something false that a wrong definition or a missing hypothesis would make true, so it
must not build. After the build, run

```
./check_controls.sh
```

For each of the 53 controls in `controls_expected.txt`, the script builds the module and checks that the build fails
with exactly one error, at the recorded position and with the recorded message. The 34 plants in
`plants_expected.txt` are wrong on purpose. Some of them are modules that build, that fail for another reason, that
fail twice or that fail in an earlier declaration. The others are controls checked against a wrong position or a
wrong message. Every plant has to be rejected. The output ends with

```
controls: 53 of 53 pass
plants: 34 of 34 rejected
```

## Axioms

`AXIOMS_ALL.txt` collects the output of `#print axioms` for the 638 theorems named in the 13 axiom-report modules,
such as `C72T1/Axioms.lean` and `C72T5/Axioms.lean`. Every one of these theorems depends on at most `propext`,
`Classical.choice` and `Quot.sound`. To see the report of one module, run for example

```
lake env lean C72T5/Axioms.lean
```

No module uses `sorry`, declares an axiom or calls `native_decide`. The finite computations are checked by `decide`,
some of them with `decide +kernel`.

## License

Apache License 2.0, see `LICENSE`.
