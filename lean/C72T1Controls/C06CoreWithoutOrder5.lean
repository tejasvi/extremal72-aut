import C72T1.Refute

/-!
# Control C06 (must not build): the final deduction without the exclusion of order 5 (Theorem A)

The cyclic group of order 5 satisfies the prime-divisor hypothesis and has no element of order 2 or 3
(`C72.Refute.core_needs_no_order5`). Expected failure: `decide` proves that `5 ≠ 5` is false.
-/

open C72

theorem C72.Controls.c06_core_without_order5 : Subgroup.zpowers Refute.c5 = ⊥ := by
  apply eq_bot_of_no_small_prime_orders
  · intro q hq hd
    exact Or.inr (Or.inr (Refute.prime_dvd_card_zpowers Nat.prime_five Refute.orderOf_c5 hq hd))
  all_goals
    intro g hg
    rcases Refute.orderOf_mem_zpowers Nat.prime_five Refute.orderOf_c5 hg with h' | h' <;> rw [h'] <;>
      decide
