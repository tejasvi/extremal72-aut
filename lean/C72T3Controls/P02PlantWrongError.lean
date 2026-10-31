import C72T3.F16

/-! Plant P02 for the control checker: one error, but not the expected `decide` message, so the checker must report
FAIL. -/

open C72.T3

theorem C72.T3.Controls.p02_plant_wrong_error : F16.t ^ 5 ≠ 1 := by
  exact fun h => h
