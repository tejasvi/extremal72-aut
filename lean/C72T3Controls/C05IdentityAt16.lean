import C72T3.Tests

/-!
# Control C05 (must not build): `H_A` is not refuted by the identity matrix at threshold 16

At threshold 4 the identity matrix refutes `H_A` (`C72.T3.Tests.not_H_Athr_four`). At threshold 16 it does not:
`M(e₀) + M(e₀ · 1) = 8` (`C72.T3.Tests.M_single_add`). The claim `M(e₀) + M(e₀ · 1) ≥ 16` must fail.
Expected failure: `decide` proves that `16 ≤ M (Pi.single 0 1) + M (Pi.single 0 1 ᵥ* 1)` is false.
-/

open C72.T3 Matrix

theorem C72.T3.Controls.c05_identity_at_16 :
    16 ≤ M (Pi.single (0 : Fin 7) (1 : F16)) + M (Pi.single (0 : Fin 7) (1 : F16) ᵥ* (1 : Matrix (Fin 7) (Fin 7) F16)) := by
  decide +kernel
