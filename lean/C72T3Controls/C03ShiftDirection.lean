import C72T3.Psi

/-!
# Control C03 (must not build): the action of `g` is multiplication by `t` with the paper's convention

With `(xg)_{g(i)} = x_i` and `g : 5a + b ↦ 5a + b + 1`, the automorphism acts on a cycle as multiplication by `t`:
`ψ(t y)_b = ψ(y)_{b-1}` (`C72.T3.psi_t_mul`, `C72.T3.permute_g5_phi1`). The other direction, `ψ(t y)_b = ψ(y)_{b+1}`,
must fail.
Expected failure: `decide` proves that `∀ (y : F16) (b : Fin 5), psi (F16.t * y) b = psi y ((finRotate 5) b)` is false.
-/

open C72.T3

theorem C72.T3.Controls.c03_shift_direction :
    ∀ (y : F16) (b : Fin 5), psi (F16.t * y) b = psi y ((finRotate 5) b) := by
  decide +kernel
