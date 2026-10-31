import C72T1.Tests

/-!
# Plant P02 for the control checker: the claim of C01 failing for a different reason (an unknown identifier).
The checker must report FAIL (wrong message).
-/

open C72 C72.Tests

theorem C72.Controls.p02_plant_wrong_error :
    permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single (c3.symm 0) 1 := by
  exact permute_c3_singel
