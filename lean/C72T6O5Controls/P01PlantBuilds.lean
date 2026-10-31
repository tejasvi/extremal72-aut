import C72T6O5.Scan

/-!
# Plant P01 for the control checker: this module builds, so the checker must report FAIL.
-/

open C72.T6O5

theorem C72.ControlsT6O5.p01_builds : scanIdx 3 0 < scanIdx 2 0 := by
  decide
