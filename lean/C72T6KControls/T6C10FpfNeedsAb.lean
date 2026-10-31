import C72T6K.Additions

/-!
# Control T6C10 (must not build): Lemma 3.4 (a) needs `a b` fixed-point-free

`C72.T6.pair_form_fpf` assumes that `b` and `a b` are fixed-point-free. For `b = aStd` (on `Fin 2 × 𝔽₂`), which commutes
with `aStd` and has no fixed point, the form `(i, e) ↦ (β i, e + t i)` has `β = 1`, which fixes every coordinate; here
`a b = 1` (`C72.T6.pair_form_fpf_needs_ab`).
Expected failure: `decide` proves that "`β 0 ≠ 0`" for `b = aStd`, i.e. `(aStd (0, 0)).1 ≠ 0`, is false.
-/

open C72.T4 in
theorem C72.Controls.t6c10_fpf_needs_ab : (aStd ((0 : Fin 2), (0 : ZMod 2))).1 ≠ 0 := by
  decide
