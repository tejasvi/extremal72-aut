import C72T6O3.M24

/-!
# Plant P02 for the control checker: the error is not the expected one (an `omega` failure), so the checker must
report FAIL.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.p02_wrong_error (n : ℕ) (h : n < 3) : n < 2 := by
  omega
