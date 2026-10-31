import C72T6O5.Scan

/-!
# Plant P04 for the control checker: the expected error occurs before the theorem's line, so the checker must
report FAIL.
-/

open C72.T6O5

example : scanIdx 2 0 < scanIdx 3 0 := by
  decide

theorem C72.ControlsT6O5.p04_after : (1 : ℕ) = 1 := by
  rfl
