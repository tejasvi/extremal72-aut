import C72T6O3.M24

/-!
# Control C03 (must not build): (N2) separates the rotations

The rotation `ρ` gives the same code as the identity but violates (N2): `ρ(p₆) = 10` is not smaller than
`ρ(p₈) = 7`.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.c03_rho_violates_n2 : rho 7 < rho 12 := by
  decide
