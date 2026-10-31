import C72T5.CB48Check

/-! Plant P03 for the control checker: the expected error and a second one, so the checker must report FAIL. -/

open C72.T5.CB48

theorem C72.T5.Controls.p03_plant_two_errors : go tets octs 8 8 0 0 0 = true := by
  decide +kernel

theorem C72.T5.Controls.p03_second : go tets octs 8 8 0 0 0 = true := by
  decide +kernel
