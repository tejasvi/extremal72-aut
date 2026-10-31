import C72T6K.KleinRefute

/-!
# Control T6C07 (must not build): Lemma 3.4 (a) needs that `b` commutes with `a`

`C72.T6.pair_form` assumes `b a = a b`. The swap `bK` of `(0, 1)` and `(1, 0)` on `Fin 2 × 𝔽₂` does not commute with
`aStd`, and it sends the two coordinates `(0, 0)`, `(0, 1)` of one pair into two different pairs, so it is not of the form
`(i, e) ↦ (β i, e + t i)` (`C72.T6.KleinRefute.pair_form_needs_commute`).
Expected failure: `decide` proves that "`bK (0, 1)` and `bK (0, 0)` lie in the same pair" is false.
-/

open C72.T6.KleinRefute

theorem C72.Controls.t6c07_pair_form_needs_commute : (bK (0, 1)).1 = (bK (0, 0)).1 := by
  decide
