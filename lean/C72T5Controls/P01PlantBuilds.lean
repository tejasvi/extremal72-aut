import C72T5.CB48Check

/-! Plant P01 for the control checker: this module builds, so the checker must report FAIL. -/

open C72.T5.CB48

theorem C72.T5.Controls.p01_plant_builds : go tets octs 6 8 0 0 0 = true :=
  go_all
