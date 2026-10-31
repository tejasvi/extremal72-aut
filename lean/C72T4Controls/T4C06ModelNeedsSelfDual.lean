import C72T4.Refute

/-!
# Control T4C06 (must not build): the model needs a self-dual contracted fixed code

For `RM(1,3)` with the translation involution, the contracted fixed code contains `a4 = 0101` and `b4 = 0011`. If it
were self-dual (the hypothesis `SelfDual Y` of `C72.T4.model`), they would be orthogonal
(`C72.T4.Refute.orthogonal_of_selfDual_Yof_RM`); they are not, and `RM(1,3)` is `C_B` for no `B`
(`C72.T4.Refute.model_needs_selfDual`).
Expected failure: `decide` proves that `a4 ⬝ᵥ b4 = 0` is false.
-/

open C72.T4.Refute

theorem C72.Controls.t4c06_model_needs_selfDual : a4 ⬝ᵥ b4 = 0 := by
  decide
