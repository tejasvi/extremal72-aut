import C72T6O3.M24

/-!
# Plant P04 for the control checker: the expected error occurs before the theorem's line, so the checker must
report FAIL.
-/

open C72 C72.Three C72.Three.M24

example : rho 7 < rho 12 := by
  decide

theorem C72.ControlsT6O3.p04_after : (1 : ℕ) = 1 := by
  rfl
