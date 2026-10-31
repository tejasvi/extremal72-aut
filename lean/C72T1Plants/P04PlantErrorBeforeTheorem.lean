import C72T1.Tests

/-!
# Plant P04 for the control checker: the expected failure sits before the theorem, and the theorem itself builds.
The checker must report FAIL (error outside the theorem).
-/

example : (2 : ℕ) ≠ 2 := by
  decide

theorem C72.Controls.p04_plant_error_before_theorem : True :=
  trivial
