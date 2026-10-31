import C72T1.Final
import C72T1.Decomp
import C72T1.Tests
import Mathlib.Tactic.NormNum.Prime

/-!
# T1: refutations of weakened statements

These theorems are the positive side of the must-fail controls (`C72T1Controls`). Each one proves
that a statement with one hypothesis dropped is false, so the hypothesis carries weight:

* the group-theoretic core of the final deduction (`eq_bot_of_no_small_prime_orders`) fails without the
  prime-divisor hypothesis (the role of `H_primes`; a cyclic group of order 7) and without each of the
  exclusions of elements of order 5, 3 and 2 (the roles of Theorems A, B and of `NoInv`; cyclic groups of
  orders 5, 3 and 2);
* the decomposition fails for `p = 2`: for the swap of two coordinates, `F ∩ E ≠ 0`;
* the contracted fixed code of a code that is not self-dual need not be self-dual (`C = 0`).
-/

namespace C72.Refute

open Equiv C72.Tests

/-! ## Helpers on cyclic subgroups -/

theorem orderOf_mem_zpowers {G : Type*} [Group G] {x y : G} {p : ℕ} (hp : p.Prime)
    (hx : orderOf x = p) (hy : y ∈ Subgroup.zpowers x) : orderOf y = 1 ∨ orderOf y = p := by
  have h := orderOf_dvd_of_mem_zpowers hy
  rw [hx] at h
  exact hp.eq_one_or_self_of_dvd _ h

theorem prime_dvd_card_zpowers {G : Type*} [Group G] {x : G} {p : ℕ} (hp : p.Prime)
    (hx : orderOf x = p) {q : ℕ} (hq : q.Prime) (hd : q ∣ Nat.card (Subgroup.zpowers x)) : q = p := by
  rw [Nat.card_zpowers, hx] at hd
  exact (Nat.prime_dvd_prime_iff_eq hq hp).1 hd

theorem zpowers_ne_bot {G : Type*} [Group G] {x : G} (hx : x ≠ 1) : Subgroup.zpowers x ≠ ⊥ := by
  intro h
  have hmem := Subgroup.mem_zpowers x
  rw [h, Subgroup.mem_bot] at hmem
  exact hx hmem

/-! ## Permutations of prime order -/

/-- The swap of the two coordinates of `Fin 2`. -/
def s2 : Perm (Fin 2) :=
  swap 0 1

/-- The 5-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`. -/
def c5 : Perm (Fin 5) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

/-- The 7-cycle `0 ↦ 1 ↦ ⋯ ↦ 6 ↦ 0`. -/
def c7 : Perm (Fin 7) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

theorem orderOf_s2 : orderOf s2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_c3 : orderOf c3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_c5 : orderOf c5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide)

theorem orderOf_c7 : orderOf c7 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide)

/-! ## The final deduction needs each of its hypotheses -/

/-- Without the prime-divisor hypothesis (`H_primes`) the deduction fails: the cyclic group of order 7 has no
element of order 2, 3 or 5. -/
theorem core_needs_primes : ¬ ∀ H : Subgroup (Perm (Fin 7)),
    (∀ g ∈ H, orderOf g ≠ 2) → (∀ g ∈ H, orderOf g ≠ 3) → (∀ g ∈ H, orderOf g ≠ 5) → H = ⊥ := by
  intro h
  have hp : (7 : ℕ).Prime := by norm_num
  refine zpowers_ne_bot (x := c7) (by decide) (h _ ?_ ?_ ?_) <;>
  · intro g hg
    rcases orderOf_mem_zpowers hp orderOf_c7 hg with h' | h' <;> rw [h'] <;> decide

/-- Without the exclusion of order 5 (Theorem A) the deduction fails: the cyclic group of order 5. -/
theorem core_needs_no_order5 : ¬ ∀ H : Subgroup (Perm (Fin 5)),
    (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 5) →
    (∀ g ∈ H, orderOf g ≠ 2) → (∀ g ∈ H, orderOf g ≠ 3) → H = ⊥ := by
  intro h
  refine zpowers_ne_bot (x := c5) (by decide) (h _ ?_ ?_ ?_)
  · intro q hq hd
    exact Or.inr (Or.inr (prime_dvd_card_zpowers Nat.prime_five orderOf_c5 hq hd))
  all_goals
    intro g hg
    rcases orderOf_mem_zpowers Nat.prime_five orderOf_c5 hg with h' | h' <;> rw [h'] <;> decide

/-- Without the exclusion of order 3 (Theorem B) the deduction fails: the cyclic group of order 3. -/
theorem core_needs_no_order3 : ¬ ∀ H : Subgroup (Perm (Fin 3)),
    (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 5) →
    (∀ g ∈ H, orderOf g ≠ 2) → (∀ g ∈ H, orderOf g ≠ 5) → H = ⊥ := by
  intro h
  refine zpowers_ne_bot (x := c3) (by decide) (h _ ?_ ?_ ?_)
  · intro q hq hd
    exact Or.inr (Or.inl (prime_dvd_card_zpowers Nat.prime_three orderOf_c3 hq hd))
  all_goals
    intro g hg
    rcases orderOf_mem_zpowers Nat.prime_three orderOf_c3 hg with h' | h' <;> rw [h'] <;> decide

/-- Without the exclusion of involutions (`NoInv`) the deduction fails: the cyclic group of order 2. -/
theorem core_needs_no_order2 : ¬ ∀ H : Subgroup (Perm (Fin 2)),
    (∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 5) →
    (∀ g ∈ H, orderOf g ≠ 3) → (∀ g ∈ H, orderOf g ≠ 5) → H = ⊥ := by
  intro h
  refine zpowers_ne_bot (x := s2) (by decide) (h _ ?_ ?_ ?_)
  · intro q hq hd
    exact Or.inl (prime_dvd_card_zpowers Nat.prime_two orderOf_s2 hq hd)
  all_goals
    intro g hg
    rcases orderOf_mem_zpowers Nat.prime_two orderOf_s2 hg with h' | h' <;> rw [h'] <;> decide

/-! ## The decomposition needs `p` odd -/

/-- For the swap `s2` of order 2 and `C = 𝔽₂²`, the word `11` lies in both `F` and `E`. -/
theorem decomposition_needs_odd :
    orderOf s2 = 2 ∧ s2 ∈ Aut (⊤ : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ∧
      Fsub ⊤ s2 ⊓ Esub ⊤ s2 ≠ ⊥ := by
  refine ⟨orderOf_s2, mem_Aut_of_map_le le_top, ?_⟩
  intro h
  have hmem : (![1, 1] : Fin 2 → ZMod 2) ∈ Fsub ⊤ s2 ⊓ Esub ⊤ s2 := by
    refine Submodule.mem_inf.2 ⟨mem_Fsub_iff.2 ⟨Submodule.mem_top, by decide⟩, ?_⟩
    exact ⟨Submodule.mem_top, by decide, by decide⟩
  rw [h, Submodule.mem_bot] at hmem
  revert hmem
  decide

/-! ## The contracted fixed code needs `C` self-dual -/

/-- For `C = 0` and the 3-cycle `c3`, the contracted fixed code is `0` on one orbit, which is not
self-dual. -/
theorem contracted_needs_selfDual :
    orderOf c3 = 3 ∧ c3 ∈ Aut (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2)) ∧
      ¬ SelfDual (contracted c3 (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2))) := by
  refine ⟨orderOf_c3, mem_Aut_of_map_le (by simp), ?_⟩
  intro h
  have h1 : (1 : Orbits c3 → ZMod 2) ∈ dual (contracted c3 (⊥ : Submodule (ZMod 2) (Fin 3 → ZMod 2))) := by
    rw [mem_dual]
    intro y hy
    have hy0 : y = 0 := by
      funext ω
      obtain ⟨i, rfl⟩ := toOrbit_surjective c3 ω
      exact congrFun ((Submodule.mem_bot _).1 ((mem_contracted c3).1 hy)) i
    rw [hy0, dotProduct_zero]
  rw [← h, mem_contracted, Submodule.mem_bot] at h1
  have h2 := congrFun h1 0
  revert h2
  decide

end C72.Refute
