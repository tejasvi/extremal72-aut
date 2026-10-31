import C72T6O3.Closure

/-!
# Control C01 (must not build): the closure certificate needs `q₁`

`M24.closeIter_F0` checks by `decide +kernel` that the fixed-point closure from `F₀ = {0, 1, 2, 3, 4, 7, 5}` reaches all
24 points. From `{0, 1, 2, 3, 4, 7}` (`p₁, …, p₆` without `q₁`, mask 159) it must not: the group `K` of order 16 fixes
these points. Expected failure: the kernel does not reduce the `Decidable` instance to `true` (the elaborator's
`decide` exceeds the default recursion depth on this computation, so the kernel is used as in `closeIter_F0`). The
positive side, `M24.Tests.closeIter_without_q1 : closeIter 2 159 ≠ FULL`, is proved in the default build.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.c01_closure_without_q1 : closeIter 2 159 = FULL := by
  decide +kernel
