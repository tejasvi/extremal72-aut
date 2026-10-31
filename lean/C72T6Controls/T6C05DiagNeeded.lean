import C72T6.Refute

/-!
# Control T6C05 (must not build): `C_B` is doubly-even only under (diag)

`C72.T6.CB_doublyEven` assumes (diag). For `B = 0` on `Y4`, which violates (diag) at `1100`, the word `(0000 | 1100)`
lies in `C_0` and has weight 2 (`C72.T6.Refute.CB_doublyEven_needs_diag`).
Expected failure: `decide` proves that `4 ∣ wt (0000 | 1100)` is false.
-/

open C72 C72.T4 C72.T6.Refute

theorem C72.Controls.t6c05_diag_needed : 4 ∣ wt (pv 0 (u1 : Fin 4 → ZMod 2)) := by
  decide
