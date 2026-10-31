import C72T4.Tests

/-!
# Control T4C01 (must not build): the involution swaps the two halves

In the pair model `a(i, e) = (i, e + 1)`, so `(u | v) a = (v | u)` (`C72.T4.permute_aStd_pv`,
`C72.T4.Tests.aStd_swaps_halves`). The claim that `a` fixes `(u | v)` is false for `u ≠ v`.
Expected failure: `decide` proves that the proposition is false.
-/

open C72 C72.T4

theorem C72.Controls.t4c01_aStd_fixes :
    permute aStd (pv (![1, 0] : Fin 2 → ZMod 2) ![0, 1]) = pv ![1, 0] ![0, 1] := by
  decide
