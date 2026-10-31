import C72T6.Refute

/-!
# Control T6C06 (must not build): `C_B` is self-dual only for symmetric `B`

`C72.T6.CB_selfDual` assumes that `B` is symmetric. For `Bn(x, x') = x₀x'₂` on `Y4` the words `(0010 | 1110)` and
`(0000 | 0011)` lie in `C_{Bn}` and are not orthogonal (`C72.T6.Refute.CB_selfDual_needs_symm`).
Expected failure: `decide` proves that the dot product of these two words is `0` is false.
-/

open C72.T4 C72.T6.Refute

theorem C72.Controls.t6c06_symmetry_needed :
    pv z1 (z1 + (u1 : Fin 4 → ZMod 2)) ⬝ᵥ pv 0 (0 + (u2 : Fin 4 → ZMod 2)) = 0 := by
  decide
