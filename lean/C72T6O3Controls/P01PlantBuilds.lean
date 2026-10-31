import C72T6O3.M24

/-!
# Plant P01 for the control checker: this module builds, so the checker must report FAIL.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.p01_builds : rho 7 = 10 := by
  decide
