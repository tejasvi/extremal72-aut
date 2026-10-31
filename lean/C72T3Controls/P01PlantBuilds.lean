import C72T3.F16

/-! Plant P01 for the control checker: this module builds, so the checker must report FAIL. -/

open C72.T3

theorem C72.T3.Controls.p01_plant_builds : F16.t ^ 5 = 1 := by
  decide
