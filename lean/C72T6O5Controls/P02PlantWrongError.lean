import C72T6O5.Scan

/-!
# Plant P02 for the control checker: the error is not the expected one (an `omega` failure), so the checker must
report FAIL.
-/

open C72.T6O5

theorem C72.ControlsT6O5.p02_wrong_error (n : ℕ) (h : n < 3) : n < 2 := by
  omega
