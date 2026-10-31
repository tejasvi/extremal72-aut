import C72T1.Tests

/-!
# Control C01 (must not build): the inverse action convention

Under the paper's convention `(x p)_{p(i)} = x_i` the unit word at `0` goes to the unit word at `c3 0 = 1`
(`C72.Tests.permute_c3_single`). The inverse convention `x p = x ∘ p` would give the unit word at
`c3⁻¹ 0 = 2`. Expected failure: `decide` proves that the proposition is false.
-/

open C72 C72.Tests

theorem C72.Controls.c01_inverse_convention :
    permute c3 (Pi.single 0 1 : Fin 3 → ZMod 2) = Pi.single (c3.symm 0) 1 := by
  decide
