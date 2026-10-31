import C72T1.Tests

/-!
# Plant P01 for the control checker: a module that builds. The checker must report FAIL (rc = 0).
-/

open C72 C72.Tests

theorem C72.Controls.p01_plant_builds :
    permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single (c3 0) 1 := by
  decide
