import C72T5.CB48Rows

/-!
# Control C03 (must not build): `E48` is self-orthogonal for the Hermitian form, not for the bilinear form

`C72.T5.CB48.erow_hform`: `Σ_j x_j ȳ_j = 0` for all rows `x, y` of `E48` (`ȳ = y²`). For the bilinear product
`Σ_j x_j y_j` some pair of rows is not orthogonal.
Expected failure: `decide` proves that `∀ (r s : Fin 8), ∑ j, erow r j * erow s j = 0` is false.
-/

open C72 C72.T5.CB48

theorem C72.T5.Controls.c03_bilinear_product : ∀ r s : Fin 8, ∑ j, erow r j * erow s j = 0 := by
  decide +kernel
