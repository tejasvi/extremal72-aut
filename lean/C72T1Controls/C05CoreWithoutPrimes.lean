import C72T1.Refute

/-!
# Control C05 (must not build): the final deduction without the prime-divisor hypothesis

The cyclic group of order 7 has no element of order 2, 3 or 5 and is not trivial
(`C72.Refute.core_needs_primes`). Feeding it to `C72.eq_bot_of_no_small_prime_orders` needs the prime 7 to be
2, 3 or 5. Expected failure: `decide` proves that `7 = 2 ∨ 7 = 3 ∨ 7 = 5` is false.
-/

open C72

theorem C72.Controls.c05_core_without_primes : Subgroup.zpowers Refute.c7 = ⊥ := by
  have hp : (7 : ℕ).Prime := by norm_num
  apply eq_bot_of_no_small_prime_orders
  · intro q hq hd
    have h7 := Refute.prime_dvd_card_zpowers hp Refute.orderOf_c7 hq hd
    subst h7
    decide
  all_goals
    intro g hg
    rcases Refute.orderOf_mem_zpowers hp Refute.orderOf_c7 hg with h' | h' <;> rw [h'] <;> decide
