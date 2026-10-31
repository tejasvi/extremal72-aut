import C72T6O3.M24
import Mathlib.Data.Fintype.CardEmbedding

/-!
# T6 (order 3): the orders of `K`, `H` and `M₂₄ = Aut G24`

From the certified facts of `C72T6O3.M24`:
* `card_K : Nat.card Kgrp = 16`: `k ↦ k(q₁)` is a bijection from `K` onto the 16 points outside `O₀`
  (onto by `kq`, one-to-one because `K` acts freely);
* `card_H : Nat.card Hgrp = 48`: `h ↦ (h(p₆), h(q₁))` is a bijection from `H` onto `{p₆, p₇, p₈} ×` (the complement
  of `O₀`);
* `card_Aut_G24 : Nat.card (Aut G24) = 244823040 = 24 · 23 · 22 · 21 · 20 · 48`: `m ↦ (m(p₁), …, m(p₅))` maps
  `Aut G24` onto the injective 5-tuples (5-transitivity), with fibres the cosets of `H`.

These are the orders the paper quotes in Section 4.3 (`|M₂₄| = 244 823 040`, the pointwise stabilisers of five
points of an octad and of the octad of orders 48 and 16).
-/

namespace C72.Three.M24

open Equiv Finset

/-- `K`, the pointwise stabiliser of `O₀` in `Aut G24`. -/
def Kgrp : Subgroup (Perm (Fin 24)) where
  carrier := {k | InK k}
  one_mem' := ⟨(Aut G24).one_mem, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨(Aut G24).mul_mem ha.1 hb.1, fun y hy => by rw [Perm.mul_apply, hb.2 y hy, ha.2 y hy]⟩
  inv_mem' := fun {a} ha =>
    ⟨(Aut G24).inv_mem ha.1, fun y hy => by rw [Perm.inv_eq_iff_eq]; exact (ha.2 y hy).symm⟩

/-- `H`, the pointwise stabiliser of `p₁, …, p₅` in `Aut G24`. -/
def Hgrp : Subgroup (Perm (Fin 24)) where
  carrier := {h | InH h}
  one_mem' := ⟨(Aut G24).one_mem, fun _ => rfl⟩
  mul_mem' := fun ha hb => InH.mul ha hb
  inv_mem' := fun ha => InH.inv ha

theorem card_compl_O0 : Fintype.card {x : Fin 24 // x ∉ O0} = 16 := by
  decide

/-- `|K| = 16`. -/
theorem card_K : Nat.card Kgrp = 16 := by
  let f : Kgrp → {x : Fin 24 // x ∉ O0} := fun k => ⟨k.1 q1, InH.apply_not_mem (InK.InH k.2) q1_spec.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab' : a.1 q1 = b.1 q1 := congrArg Subtype.val hab
      have hq : (a.1⁻¹ * b.1) q1 = q1 := by
        rw [Perm.mul_apply, ← hab', Perm.inv_def, Equiv.symm_apply_apply]
      have h1 := InK_eq_one (Kgrp.mul_mem (Kgrp.inv_mem a.2) b.2) hq
      exact Subtype.ext (inv_mul_eq_one.1 h1)
    · intro x
      obtain ⟨hk, hkfix, hkq⟩ := kq_spec x.1 x.2
      exact ⟨⟨kq x.1, hk, hkfix⟩, Subtype.ext hkq⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, card_compl_O0]

/-- `|H| = 48`. -/
theorem card_H : Nat.card Hgrp = 48 := by
  have hr7 : rho 7 = 10 := rho_spec.2.2.1
  have hr10 : rho 10 = 12 := rho_spec.2.2.2.1
  have h7 : (7 : Fin 24) ∈ O0 := by rw [O0_eq]; decide
  have hP : ∀ h : Perm (Fin 24), InH h → h 7 ∈ ({7, 10, 12} : Finset (Fin 24)) := fun h hh => by
    obtain ⟨j, hj3, hj⟩ := InH_eq_rho_pow_mul hh
    have hm : h 7 = (rho ^ j) 7 := by
      have := hj.2 7 h7
      rw [Perm.mul_apply, Perm.inv_eq_iff_eq] at this
      exact this
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [hm]; decide
    · rw [hm, pow_one, hr7]; decide
    · rw [hm, pow_two, Perm.mul_apply, hr7, hr10]; decide
  let f : Hgrp → {a : Fin 24 // a ∈ ({7, 10, 12} : Finset (Fin 24))} × {x : Fin 24 // x ∉ O0} :=
    fun h => (⟨h.1 7, hP h.1 h.2⟩, ⟨h.1 q1, InH.apply_not_mem h.2 q1_spec.1⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h7' : a.1 7 = b.1 7 := congrArg (fun p => p.1.1) hab
      have hq' : a.1 q1 = b.1 q1 := congrArg (fun p => p.2.1) hab
      have hH : InH (a.1⁻¹ * b.1) := InH.mul (InH.inv a.2) b.2
      have hK : InK (a.1⁻¹ * b.1) := InK_of_InH hH (by rw [Perm.mul_apply, ← h7', Perm.inv_def, Equiv.symm_apply_apply])
      have h1 := InK_eq_one hK (by rw [Perm.mul_apply, ← hq', Perm.inv_def, Equiv.symm_apply_apply])
      exact Subtype.ext (inv_mul_eq_one.1 h1)
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      -- choose `j` with `ρʲ(p₆) = a`, then `x = ρ⁻ʲ(b)` outside `O₀`
      have hex : ∃ j : ℕ, (rho ^ j) 7 = a := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, by rw [pow_one, hr7]⟩
        · exact ⟨2, by rw [pow_two, Perm.mul_apply, hr7, hr10]⟩
      obtain ⟨j, hj⟩ := hex
      have hHj : InH (rho ^ j) := rho_InH.pow j
      have hx : (rho ^ j)⁻¹ b ∉ O0 := InH.apply_not_mem (InH.inv hHj) hb
      obtain ⟨hk, hkfix, hkq⟩ := kq_spec _ hx
      refine ⟨⟨rho ^ j * kq ((rho ^ j)⁻¹ b), InH.mul hHj (InK.InH ⟨hk, hkfix⟩)⟩, ?_⟩
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show (rho ^ j * kq ((rho ^ j)⁻¹ b)) 7 = a
        rw [Perm.mul_apply, hkfix 7 h7, hj]
      · show (rho ^ j * kq ((rho ^ j)⁻¹ b)) q1 = b
        rw [Perm.mul_apply, hkq, Perm.inv_def, Equiv.apply_symm_apply]
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_prod]
  decide

/-- A chosen element of `Aut G24` mapping `p₁, …, p₅` to a given injective 5-tuple. -/
noncomputable def tsec (f : Fin 5 ↪ Fin 24) : Perm (Fin 24) :=
  Classical.choose (five_transitive f f.injective)

theorem tsec_spec (f : Fin 5 ↪ Fin 24) : tsec f ∈ Aut G24 ∧ ∀ i, tsec f (bp i) = f i :=
  Classical.choose_spec (five_transitive f f.injective)

/-- The 5-tuple `(m(p₁), …, m(p₅))`. -/
def tupleOf (m : Perm (Fin 24)) : Fin 5 ↪ Fin 24 :=
  ⟨fun i => m (bp i), fun i j hij => by
    have h := m.injective hij
    exact Fin.ext (by have := congrArg Fin.val h; rwa [bp_val, bp_val] at this)⟩

/-- **`|M₂₄| = 244 823 040`.** -/
theorem card_Aut_G24 : Nat.card (Aut G24) = 244823040 := by
  have hH : ∀ m : Aut G24, (tsec (tupleOf m.1))⁻¹ * m.1 ∈ Hgrp := fun m =>
    ⟨(Aut G24).mul_mem ((Aut G24).inv_mem (tsec_spec _).1) m.2, fun j => by
      rw [Perm.mul_apply, Perm.inv_eq_iff_eq, (tsec_spec _).2]
      rfl⟩
  let Φ : Aut G24 → (Fin 5 ↪ Fin 24) × Hgrp := fun m => (tupleOf m.1, ⟨_, hH m⟩)
  let Ψ : (Fin 5 ↪ Fin 24) × Hgrp → Aut G24 := fun p =>
    ⟨tsec p.1 * p.2.1, (Aut G24).mul_mem (tsec_spec p.1).1 p.2.2.1⟩
  have hΨΦ : ∀ m, Ψ (Φ m) = m := fun m => Subtype.ext (by simp [Φ, Ψ])
  have htuple : ∀ p : (Fin 5 ↪ Fin 24) × Hgrp, tupleOf (tsec p.1 * p.2.1) = p.1 := fun p => by
    refine Function.Embedding.ext fun i => ?_
    show (tsec p.1 * p.2.1) (bp i) = p.1 i
    rw [Perm.mul_apply, p.2.2.2 i, (tsec_spec p.1).2]
  have hΦΨ : ∀ p, Φ (Ψ p) = p := fun p => by
    refine Prod.ext (htuple p) (Subtype.ext ?_)
    show (tsec (tupleOf (tsec p.1 * p.2.1)))⁻¹ * (tsec p.1 * p.2.1) = p.2.1
    rw [htuple p, ← mul_assoc, inv_mul_cancel, one_mul]
  have e : Aut G24 ≃ (Fin 5 ↪ Fin 24) × Hgrp := ⟨Φ, Ψ, hΨΦ, hΦΨ⟩
  rw [Nat.card_congr e, Nat.card_prod, card_H, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin]
  rfl

end C72.Three.M24
