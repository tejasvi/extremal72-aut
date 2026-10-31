import C72T1.Refute

/-!
# Control C09 (must not build): the contracted fixed code of a code that is not self-dual

`C72.contracted_selfDual` needs `SelfDual C`. For `C = 0` and the 3-cycle `c3` the contracted fixed code is not
self-dual (`C72.Refute.contracted_needs_selfDual`). Discharging `SelfDual 0` by the dimension criterion needs
`2 * 0 = 3`. Expected failure: `decide` proves that `2 * 0 = 3` is false.
-/

open C72

theorem C72.Controls.c09_contracted_without_selfDual :
    SelfDual (contracted Tests.c3 (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2))) :=
  contracted_selfDual Tests.c3 Nat.prime_three (by decide) Refute.orderOf_c3 (mem_Aut_of_map_le (by simp))
    (selfDual_of_le_of_two_mul_finrank bot_le (by rw [finrank_bot, Fintype.card_fin]; decide))
