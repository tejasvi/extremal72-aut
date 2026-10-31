import C72T1.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# T1 skeleton: the final deduction of the Main Theorem

The paper proves the Main Theorem as follows. By the literature [Bor15, Thm 6.3] the automorphism group is
trivial, `C₂`, `C₃`, `C₂ × C₂` or `C₅`; by (L1) and Theorem D it has no involution, and Theorems A and B exclude
elements of order 5 and 3.

Here the list of groups is replaced by the weaker named hypothesis `H_primes` (every prime divisor of `|Aut C|`
is 2, 3 or 5). Cauchy's theorem (`exists_prime_orderOf_dvd_card'`) then gives an element of order 2, 3 or 5,
which the named hypotheses for Theorems A, B and D exclude.

The named hypotheses below are `def`s of type `Prop`. Nothing here assumes them: they are explicit premises
of `main_of_parts` and `main_of_cited`.
-/

namespace C72

/-! ## Named hypotheses -/

/-- **H_primes** (cited): every prime divisor of `|Aut C|` is 2, 3 or 5. It is implied by [Bor15, Thm 6.3]
(the group is trivial, `C₂`, `C₃`, `C₂ × C₂` or `C₅`) and is weaker than it. -/
def H_primes : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ p : ℕ, p.Prime → p ∣ Nat.card (Aut C) → p = 2 ∨ p = 3 ∨ p = 5

/-- **Theorem A** of the paper: no automorphism of order 5. -/
def ThmA : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g ≠ 5

/-- **Theorem B** of the paper: no automorphism of order 3. -/
def ThmB : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g ≠ 3

/-- **H_L1** (cited, (L1) in Section 3 of the paper, [Bou02]): every involution in `Aut C` is
fixed-point-free. -/
def H_L1 : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → ∀ i, a i ≠ i

/-- **NoFPFInv**: `Aut C` has no fixed-point-free involution. In the paper this is Theorem D together with
(L2) [Nebe12, Thm 3.1] and (L3) [AMG08, HM12]: the contracted fixed code of a fixed-point-free involution is
a self-dual `[36,18,8]` code, hence equivalent to one of the 41 codes `Y`, and Theorem D excludes each `Y`. -/
def NoFPFInv : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → ¬ ∀ i, a i ≠ i

/-- No automorphism of order 2. -/
def NoInv : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a ≠ 2

/-! ## `Aut C` is finite, so `Nat.card (Aut C)` is its order -/

instance instFiniteAut {n : ℕ} (C : Code n) : Finite (Aut C) :=
  inferInstance

/-- `Nat.card (Aut C)` is the true order of `Aut C` (no junk value `0`). -/
theorem card_Aut_pos {n : ℕ} (C : Code n) : 0 < Nat.card (Aut C) :=
  Nat.card_pos

/-! ## The group-theoretic core -/

/-- A finite subgroup whose order has no prime divisor other than 2, 3 and 5, and which has no element of
order 2, 3 or 5, is trivial (Cauchy's theorem). -/
theorem eq_bot_of_no_small_prime_orders {G : Type*} [Group G] (H : Subgroup G) [Finite H]
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 ∨ p = 5)
    (h2 : ∀ g ∈ H, orderOf g ≠ 2) (h3 : ∀ g ∈ H, orderOf g ≠ 3) (h5 : ∀ g ∈ H, orderOf g ≠ 5) :
    H = ⊥ := by
  by_contra hne
  have hcard : Nat.card H ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq H h)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx' : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hx
  rcases hprimes p hp hdvd with rfl | rfl | rfl
  · exact h2 x x.2 hx'
  · exact h3 x x.2 hx'
  · exact h5 x x.2 hx'

/-! ## The final deduction -/

/-- (L1) and "no fixed-point-free involution" exclude involutions. -/
theorem noInv_of (hL1 : H_L1) (hD : NoFPFInv) : NoInv :=
  fun C hC a ha h2 => hD C hC a ha h2 (hL1 C hC a ha h2)

/-- **The final deduction.** If every prime divisor of `|Aut C|` is 2, 3 or 5 and `Aut C` has no element of
order 2, 3 or 5, then `Aut C` is trivial. -/
theorem main_of_parts (h1 : H_primes) (hA : ThmA) (hB : ThmB) (hI : NoInv) :
    ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  fun C hC => eq_bot_of_no_small_prime_orders (Aut C) (h1 C hC) (hI C hC) (hB C hC) (hA C hC)

/-- The Main Theorem from the named hypotheses `H_primes`, `H_L1`, `ThmA`, `ThmB` and `NoFPFInv`. -/
theorem main_of_cited (h1 : H_primes) (hL1 : H_L1) (hA : ThmA) (hB : ThmB) (hD : NoFPFInv) :
    ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  main_of_parts h1 hA hB (noInv_of hL1 hD)

end C72
