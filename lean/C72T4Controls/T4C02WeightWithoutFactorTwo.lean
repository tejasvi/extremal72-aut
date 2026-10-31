import C72T4.Tests

/-!
# Control T4C02 (must not build): Lemma 3.3 (a) without the factor 2

`|(z | z + y)| = |y| + 2 |z ∖ supp y|` (`C72.T4.wt_pv_add`). Without the factor 2 the formula is false: for
`z = 100`, `y = 011` the word `(100 | 111)` has weight 4, not `2 + 1`.
Expected failure: `decide` proves that the proposition is false.
-/

open C72 C72.T4

theorem C72.Controls.t4c02_weight_without_factor_two :
    wt (pv (![1, 0, 0] : Fin 3 → ZMod 2) (![1, 0, 0] + ![0, 1, 1])) = wt (![0, 1, 1] : Fin 3 → ZMod 2) + 1 := by
  decide
