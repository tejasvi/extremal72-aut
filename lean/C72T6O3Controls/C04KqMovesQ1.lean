import C72T6O3.M24

/-!
# Control C04 (must not build): (N3) is needed for uniqueness

`kq 6 ∈ K` fixes `O₀` pointwise, so it preserves (N1) and (N2), but it moves `q₁ = 5` to 6.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.Three C72.Three.M24

theorem C72.ControlsT6O3.c04_kq_moves_q1 : kq 6 q1 = q1 := by
  decide
