import C72T3.F16

/-!
# Control C02 (must not build): `t` has order 5, it is not a primitive element of `𝔽₁₆^×`

`C72.T3.F16.t_pow_five` proves `t⁵ = 1` (and `orderOf_t`: the order is 5). The claim `t⁵ ≠ 1` must fail.
Expected failure: `decide` proves that `F16.t ^ 5 ≠ 1` is false.
-/

open C72.T3

theorem C72.T3.Controls.c02_t_primitive : F16.t ^ 5 ≠ 1 := by
  decide
