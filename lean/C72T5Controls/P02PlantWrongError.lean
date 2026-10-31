import C72T5.CB48Check

/-! Plant P02 for the control checker: one error, but not the expected `decide` message, so the checker must report
FAIL. -/

open C72.T5.CB48

theorem C72.T5.Controls.p02_plant_wrong_error : go tets octs 8 8 0 0 0 = true := by
  exact go_all
