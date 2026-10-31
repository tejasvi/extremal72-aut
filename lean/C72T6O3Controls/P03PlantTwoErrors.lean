import C72T6O3.M24

/-!
# Plant P03 for the control checker: two errors (the expected one and a second), so the checker must report FAIL.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.p03_two_errors : rho 7 < rho 12 := by
  decide

theorem C72.ControlsT6O3.p03_second : (1 : ℕ) = 2 := by
  decide
