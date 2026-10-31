import C72T2.Coords

/-!
# Control C05 (must not build): the direction of the action of `σ` on `φ(e)`

`Three.Tests.sigma3_phi_example` proves `φ(e) σ = φ(ω e)` for `e = (1, 0, …, 0)` by `permute_sigma3_phi`. With
`ω̄` in place of `ω` the same proof must fail at the last step.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three C72.F4

theorem C72.ControlsT2.c05_shift_direction :
    permute sigma3 (phi (Pi.single 0 1)) = phi (Pi.single 0 F4.wb) := by
  rw [permute_sigma3_phi]
  congr 1
  decide
