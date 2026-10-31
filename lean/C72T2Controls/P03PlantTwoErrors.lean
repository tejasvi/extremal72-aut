import C72T2.F4

/-!
# Plant P03 for the control checker: two errors (the expected one and a second), so the checker must report FAIL.
-/

open C72 C72.F4

theorem C72.ControlsT2.p03_two_errors : ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * v) := by
  decide

theorem C72.ControlsT2.p03_second : (1 : ℕ) = 2 := by
  decide
