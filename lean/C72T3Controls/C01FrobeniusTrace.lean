import C72T3.Psi

/-!
# Control C01 (must not build): the conjugation is `y ↦ y⁴`, not the Frobenius `y ↦ y²`

The binary inner product of `ψ(y)` and `ψ(y')` is `Tr(y ȳ')` with `ȳ = y⁴` (`C72.T3.dot_psi`). With the Frobenius
`y'²` in place of `ȳ'` the identity fails.
Expected failure: `decide` proves that `∀ (y y' : F16), psi y ⬝ᵥ psi y' = tr (y * y' ^ 2)` is false.
-/

open C72.T3

theorem C72.T3.Controls.c01_frobenius_trace : ∀ y y' : F16, psi y ⬝ᵥ psi y' = tr (y * y' ^ 2) := by
  decide +kernel
