import C72T2.F4

/-!
# Control C02 (must not build): `σ` acts on a cycle as multiplication by `ω`, not by `ω̄`

`F4.psi_w_mul` proves `ψ(ω u)_b = ψ(u)_{b-1}` by `decide`. The same proof must fail for `ω̄`.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.F4

theorem C72.ControlsT2.c02_action_conjugate : ∀ (u : F4) (b : Fin 3), psi (F4.wb * u) b = psi u (b - 1) := by
  decide
