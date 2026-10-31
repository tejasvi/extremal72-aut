import C72T2.F4

/-!
# Plant P01 for the control checker: this module builds, so the checker must report FAIL.
-/

open C72 C72.F4

theorem C72.ControlsT2.p01_builds : ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * star v) := by
  decide
