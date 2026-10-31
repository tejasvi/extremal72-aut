import C72T1.Refute

/-!
# Control C07 (must not build): the final deduction without the exclusion of order 3 (Theorem B)

The cyclic group of order 3 satisfies the prime-divisor hypothesis and has no element of order 2 or 5
(`C72.Refute.core_needs_no_order3`). Expected failure: `decide` proves that `3 ≠ 3` is false.
-/

open C72

theorem C72.Controls.c07_core_without_order3 : Subgroup.zpowers Tests.c3 = ⊥ := by
  apply eq_bot_of_no_small_prime_orders
  · intro q hq hd
    exact Or.inr (Or.inl (Refute.prime_dvd_card_zpowers Nat.prime_three Refute.orderOf_c3 hq hd))
  all_goals
    intro g hg
    rcases Refute.orderOf_mem_zpowers Nat.prime_three Refute.orderOf_c3 hg with h' | h' <;> rw [h'] <;>
      decide
