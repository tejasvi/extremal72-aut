import C72T2.F4

/-!
# Plant P02 for the control checker: the error is not the expected one (an `omega` failure), so the checker must
report FAIL.
-/

open C72 C72.F4

theorem C72.ControlsT2.p02_wrong_error (n : ℕ) (h : n < 3) : n < 2 := by
  omega
