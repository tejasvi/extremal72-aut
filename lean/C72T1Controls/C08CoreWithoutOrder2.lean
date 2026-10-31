import C72T1.Refute

/-!
# Control C08 (must not build): the final deduction without the exclusion of involutions (`NoInv`)

The cyclic group of order 2 satisfies the prime-divisor hypothesis and has no element of order 3 or 5
(`C72.Refute.core_needs_no_order2`). Expected failure: `decide` proves that `2 ≠ 2` is false.
-/

open C72

theorem C72.Controls.c08_core_without_order2 : Subgroup.zpowers Refute.s2 = ⊥ := by
  apply eq_bot_of_no_small_prime_orders
  · intro q hq hd
    exact Or.inl (Refute.prime_dvd_card_zpowers Nat.prime_two Refute.orderOf_s2 hq hd)
  all_goals
    intro g hg
    rcases Refute.orderOf_mem_zpowers Nat.prime_two Refute.orderOf_s2 hg with h' | h' <;> rw [h'] <;>
      decide
