import C72T1.Tests

/-!
# Plant P03 for the control checker: the claim of C01 plus a second false claim, so two errors.
The checker must report FAIL (two errors).
-/

open C72 C72.Tests

theorem C72.Controls.p03_plant_two_errors :
    permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single (c3.symm 0) 1 ∧ (2 : ℕ) ≠ 2 := by
  constructor
  · decide
  · decide
