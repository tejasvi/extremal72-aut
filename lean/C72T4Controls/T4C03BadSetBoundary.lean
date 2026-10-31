import C72T4.Tests

/-!
# Control T4C03 (must not build): arithmetic at the boundary of the bad set (does not test `H_D`)

`H_D` uses the program's patterns `2|e| < 16 - |y|`, and Lemma 3.6 then gives a word of weight `|y| + 2|e| < 16`. For a
constraint word of weight 8 and a pattern of 4 positions (`2|e| = 16 - |y|`) the word has weight `8 + 2 * 4 = 16`, which
does not contradict minimum weight 16. The claim below is this arithmetic only: it refers to no T4 definition, and the
bound of `H_D` is checked by reading.
Expected failure: `decide` proves that `8 + 2 * 4 < 16` is false.
-/

theorem C72.Controls.t4c03_bad_set_boundary : 8 + 2 * 4 < 16 := by
  decide
