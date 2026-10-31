import C72T2.F4

/-!
# Plant P04 for the control checker: the expected error occurs before the theorem's line, so the checker must
report FAIL.
-/

open C72 C72.F4

example : ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * v) := by
  decide

theorem C72.ControlsT2.p04_after : (1 : ℕ) = 1 := by
  rfl
