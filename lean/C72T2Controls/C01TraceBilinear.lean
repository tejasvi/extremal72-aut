import C72T2.F4

/-!
# Control C01 (must not build): the trace identity needs the conjugation

`F4.psi_dot` proves `⟨ψ(u), ψ(v)⟩ = Tr(u v̄)` by `decide`. With the bilinear product `u v` in place of `u v̄` the
same proof must fail: at `u = v = ω`, `⟨ψ(ω), ψ(ω)⟩ = 0` but `Tr(ω²) = Tr(ω̄) = 1`.
Expected failure: `decide` proves that the statement is false.
-/

open C72 C72.F4

theorem C72.ControlsT2.c01_trace_bilinear : ∀ u v : F4, ∑ b : Fin 3, psi u b * psi v b = tr (u * v) := by
  decide
