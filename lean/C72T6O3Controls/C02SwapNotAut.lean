import C72T6O3.Perm24

/-!
# Control C02 (must not build): the automorphism check rejects a non-automorphism

`M24.autOK` accepts the 127 automorphisms of `C72T6O3.M24Data`. For the transposition `(0 1)` it must return
`false` (the image of the first generator differs from it in two points).
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.c02_swap_not_aut : autOK (Equiv.swap (0 : Fin 24) 1) = true := by
  decide
