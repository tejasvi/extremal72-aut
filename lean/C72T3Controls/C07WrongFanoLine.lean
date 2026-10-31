import C72T3.MDef

/-!
# Control C07 (must not build): the data of `e8` pin the Fano lines

The 16 words of `e8Words` (lines `{0,1,3}`, `{1,2,4}`, …) lie in the paper's `e8` (`C72.T3.wordVec_dot`). The word
`({0, 1, 2}, 1)`, for a triple that is not a line, does not: the claim that it passes the parity checks of `e8`
must fail.
Expected failure: `decide` proves that `∀ (j : Fin 4), wordVec ({0, 1, 2}, 1) ⬝ᵥ C72.Tests.e8gen j = 0` is false.
-/

open C72 C72.T3

theorem C72.T3.Controls.c07_wrong_fano_line :
    ∀ j : Fin 4, wordVec ({0, 1, 2}, 1) ⬝ᵥ C72.Tests.e8gen j = 0 := by
  decide +kernel
