import C72T6O5.Scan

/-!
# Plant P03 for the control checker: two errors (the expected one and a second), so the checker must report FAIL.
-/

open C72.T6O5

theorem C72.ControlsT6O5.p03_two_errors : scanIdx 2 0 < scanIdx 3 0 := by
  decide

theorem C72.ControlsT6O5.p03_second : (1 : ℕ) = 2 := by
  decide
