import C72T6.Refute

/-!
# Control T6C02 (must not build): the slice property needs the pivot condition

`C72.T6.slice_existsUnique` uses the pivot condition `φ i (D j) = δ_ij`. For `G = span{11}` and `ψ(v) = v₀ + v₁` it fails
(`ψ(11) = 0`), and the coset `10 + G` does not meet `{ψ = 0}` (`C72.T6.Refute.slice_needs_pivot`).
Expected failure: `decide` proves that `∃ t, ψ(10 + t · 11) = 0` is false.
-/

open C72.T6.Refute

theorem C72.Controls.t6c02_pivot_needed : ∃ t : ZMod 2, ψ2 (![1, 0] + t • d2) = 0 := by
  decide
