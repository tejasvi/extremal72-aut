import C72T3.F16

/-! Plant P03 for the control checker: the expected error and a second one, so the checker must report FAIL. -/

open C72.T3

theorem C72.T3.Controls.p03_plant_two_errors : F16.t ^ 5 ≠ 1 := by
  decide

theorem C72.T3.Controls.p03_second : F16.t ^ 5 ≠ 1 := by
  decide
