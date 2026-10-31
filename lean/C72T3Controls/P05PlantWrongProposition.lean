import C72T3.F16

/-! Plant P05 for the control checker: the `decide` message at the expected position, but for another
proposition than the expected one, so the checker must report FAIL. -/

open C72.T3

theorem C72.T3.Controls.p05_plant_wrong_proposition : F16.t ^ 3 = 1 := by
  decide
