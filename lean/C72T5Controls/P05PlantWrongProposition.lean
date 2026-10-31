import C72T5.CB48Check

/-! Plant P05 for the control checker: the `decide` message at the expected position, but for another
proposition than the expected one, so the checker must report FAIL. -/

open C72.T5.CB48

theorem C72.T5.Controls.p05_plant_wrong_proposition : go tets octs 7 8 0 0 0 = true := by
  decide +kernel
