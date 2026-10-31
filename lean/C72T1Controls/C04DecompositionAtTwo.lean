import C72T1.Refute

/-!
# Control C04 (must not build): the decomposition at `p = 2`

`C72.Fsub_inf_Esub` needs `p ≠ 2`. For the swap `s2` of order 2 on `𝔽₂²` the conclusion `F ∩ E = 0` is false
(`C72.Refute.decomposition_needs_odd`). Expected failure: `decide` proves that `2 ≠ 2` is false.
-/

open C72

theorem C72.Controls.c04_decomposition_at_two :
    Fsub (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) Refute.s2 ⊓ Esub ⊤ Refute.s2 = ⊥ :=
  Fsub_inf_Esub Nat.prime_two (by decide) Refute.orderOf_s2
