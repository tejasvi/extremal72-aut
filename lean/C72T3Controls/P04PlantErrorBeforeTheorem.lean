import C72T3.F16

/-! Plant P04 for the control checker: the only error is in an earlier declaration, not at the expected position,
so the checker must report FAIL. -/

open C72.T3

theorem C72.T3.Controls.p04_earlier : F16.t ^ 5 ≠ 1 := by
  decide

theorem C72.T3.Controls.p04_plant_error_before_theorem : F16.t ^ 5 = 1 := by
  decide
