import C72T5.CB48Check

/-! Plant P04 for the control checker: the only error is in an earlier declaration, not at the expected position,
so the checker must report FAIL. -/

open C72.T5.CB48

theorem C72.T5.Controls.p04_earlier : go tets octs 8 8 0 0 0 = true := by
  decide +kernel

theorem C72.T5.Controls.p04_plant_error_before_theorem : go tets octs 6 8 0 0 0 = true :=
  go_all
