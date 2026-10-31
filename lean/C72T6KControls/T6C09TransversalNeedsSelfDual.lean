import C72T6K.KleinRefute

/-!
# Control T6C09 (must not build): Lemma 3.5 (b) for a transversal needs `Y` self-dual

`C72.T6.formAct_DT_of_transversal` assumes `Y` self-dual (`|y ∩ y'|` even). On the full space `𝔽₂²`, with `β = (0 1)` and
`T = {0}` (one element of the orbit `{0, 1}`), `D_T^β(10, 10) = 0` and `D_T(10, 10) = 1`
(`C72.T6.KleinRefute.transversal_needs_selfDual`).
Expected failure: `decide` proves that `D_{{0}}^β(10, 10) = D_{{0}}(10, 10)` is false.
-/

open C72.T6 C72.T6.KleinRefute

theorem C72.Controls.t6c09_transversal_needs_selfDual : formAct βF (DT ⊤ {0}) y10 y10 = DT ⊤ {0} y10 y10 := by
  decide
