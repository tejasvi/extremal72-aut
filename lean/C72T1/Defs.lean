import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# T1 definitions: codes, weight, duality, Type II, extremal `[72,36,16]`, automorphisms

The conventions are those of the paper (subsection "Conventions" of Section 1):

* a binary code of length `n` is a subspace of `𝔽₂ⁿ`, here `Code n := Submodule (ZMod 2) (Fin n → ZMod 2)`;
* `wt x` is the Hamming weight `|x|` and `x ⬝ᵥ y = ∑ i, x i * y i` is `⟨x, y⟩`;
* a permutation `p` of the coordinates acts by `(x p)_{p(i)} = x_i`, that is `x p = x ∘ p⁻¹`;
  in Lean this is `permute p x`, and `permute p x (p i) = x i` (`permute_apply_self`);
* the code `C p` is `C.map (permute p).toLinearMap`, and `Aut C` is the group of the permutations `p`
  with `C p = C`;
* two codes are equivalent if a permutation maps one onto the other (`PermEquiv`).

Duality, the action and `Aut` are defined over any commutative ring `K` and any finite index type `ι`,
because the contracted fixed code of `C72T1.Decomp` is indexed by the orbits of a permutation.
For binary codes of length `n` take `K = ZMod 2` and `ι = Fin n`.

With `permute`, the Lean product `p * q` (first `q`, then `p`) acts as `permute (p * q) = permute p ∘ permute q`
(`permute_mul`). In the paper's right action the same map is written `x ↦ (x q) p`. The group `Aut C` as a set
and the orders of its elements do not depend on this.
-/

namespace C72

open Module

section General

variable {K : Type*} {ι : Type*}

/-! ### The action of a permutation on words -/

/-- The paper's action of a permutation `p` on words: `(x p)_{p(i)} = x_i`, i.e. `x p = x ∘ p⁻¹`. -/
def permute [Semiring K] (p : Equiv.Perm ι) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearEquiv.funCongrLeft K K p.symm

@[simp]
theorem permute_apply [Semiring K] (p : Equiv.Perm ι) (x : ι → K) (i : ι) :
    permute p x i = x (p.symm i) :=
  rfl

/-- The paper's convention `(x p)_{p(i)} = x_i`. -/
theorem permute_apply_self [Semiring K] (p : Equiv.Perm ι) (x : ι → K) (i : ι) :
    permute p x (p i) = x i := by
  simp

theorem permute_one_apply [Semiring K] (x : ι → K) : permute (1 : Equiv.Perm ι) x = x :=
  rfl

theorem permute_mul [Semiring K] (p q : Equiv.Perm ι) (x : ι → K) :
    permute (p * q) x = permute p (permute q x) :=
  rfl

/-- `permute (q⁻¹) x = x ∘ q`. -/
theorem permute_inv_apply [Semiring K] (q : Equiv.Perm ι) (x : ι → K) (i : ι) :
    permute q⁻¹ x i = x (q i) :=
  rfl

theorem map_permute_one [Semiring K] (C : Submodule K (ι → K)) :
    C.map (permute (1 : Equiv.Perm ι)).toLinearMap = C := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem map_permute_mul [Semiring K] (C : Submodule K (ι → K)) (p q : Equiv.Perm ι) :
    C.map (permute (p * q)).toLinearMap =
      (C.map (permute q).toLinearMap).map (permute p).toLinearMap := by
  ext x
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨permute q y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/-! ### The permutation automorphism group -/

/-- `Aut C`: the permutations `p` of the coordinates with `C p = C`. -/
def Aut [Semiring K] (C : Submodule K (ι → K)) : Subgroup (Equiv.Perm ι) where
  carrier := {p | C.map (permute p).toLinearMap = C}
  one_mem' := map_permute_one C
  mul_mem' := by
    intro p q hp hq
    have hp' : C.map (permute p).toLinearMap = C := hp
    have hq' : C.map (permute q).toLinearMap = C := hq
    show C.map (permute (p * q)).toLinearMap = C
    rw [map_permute_mul, hq', hp']
  inv_mem' := by
    intro p hp
    have hp' : C.map (permute p).toLinearMap = C := hp
    show C.map (permute p⁻¹).toLinearMap = C
    calc C.map (permute p⁻¹).toLinearMap
        = (C.map (permute p).toLinearMap).map (permute p⁻¹).toLinearMap := by rw [hp']
      _ = C.map (permute (p⁻¹ * p)).toLinearMap := (map_permute_mul C p⁻¹ p).symm
      _ = C := by rw [inv_mul_cancel, map_permute_one]

theorem mem_Aut [Semiring K] {C : Submodule K (ι → K)} {p : Equiv.Perm ι} :
    p ∈ Aut C ↔ C.map (permute p).toLinearMap = C :=
  Iff.rfl

theorem permute_mem_of_mem_Aut [Semiring K] {C : Submodule K (ι → K)} {p : Equiv.Perm ι}
    (hp : p ∈ Aut C) {x : ι → K} (hx : x ∈ C) : permute p x ∈ C := by
  rw [← mem_Aut.1 hp]
  exact Submodule.mem_map_of_mem hx

/-- Two codes are equivalent if a permutation of the coordinates maps one onto the other. -/
def PermEquiv [Semiring K] (C D : Submodule K (ι → K)) : Prop :=
  ∃ p : Equiv.Perm ι, C.map (permute p).toLinearMap = D

/-- The automorphism group of a permuted code is the conjugate group:
`p ∈ Aut (C π) ↔ π⁻¹ * p * π ∈ Aut C`, i.e. `Aut (C π) = π Aut(C) π⁻¹` in Lean's product. -/
theorem mem_Aut_map_permute_iff [Semiring K] (C : Submodule K (ι → K)) (π p : Equiv.Perm ι) :
    p ∈ Aut (C.map (permute π).toLinearMap) ↔ π⁻¹ * p * π ∈ Aut C := by
  simp only [mem_Aut]
  constructor
  · intro h
    calc C.map (permute (π⁻¹ * p * π)).toLinearMap
        = ((C.map (permute π).toLinearMap).map (permute p).toLinearMap).map
            (permute π⁻¹).toLinearMap := by
          rw [mul_assoc, map_permute_mul, map_permute_mul]
      _ = C := by rw [h, ← map_permute_mul, inv_mul_cancel, map_permute_one]
  · intro h
    calc (C.map (permute π).toLinearMap).map (permute p).toLinearMap
        = C.map (permute (π * (π⁻¹ * p * π))).toLinearMap := by
          rw [← map_permute_mul]
          congr 3
          group
      _ = C.map (permute π).toLinearMap := by rw [map_permute_mul, h]

/-- The same statement as an equality of subgroups: `Aut (C π) = π Aut(C) π⁻¹`. -/
theorem Aut_map_permute [Semiring K] (C : Submodule K (ι → K)) (π : Equiv.Perm ι) :
    Aut (C.map (permute π).toLinearMap) = (Aut C).map (MulAut.conj π).toMonoidHom := by
  ext p
  rw [mem_Aut_map_permute_iff, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨π⁻¹ * p * π, h, by simp [mul_assoc]⟩
  · rintro ⟨q, hq, rfl⟩
    simpa [mul_assoc] using hq

/-! ### Weight and the dot product -/

/-- The Hamming weight `|x|`. -/
def wt [Fintype ι] [Zero K] [DecidableEq K] (x : ι → K) : ℕ :=
  hammingNorm x

theorem wt_permute [Fintype ι] [Semiring K] [DecidableEq K] (p : Equiv.Perm ι) (x : ι → K) :
    wt (permute p x) = wt x := by
  unfold wt hammingNorm
  refine Finset.card_bij (fun i _ => p.symm i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_univ _, hi.2⟩
  · intro i _ j _ h
    exact p.symm.injective h
  · intro j hj
    rw [Finset.mem_filter] at hj
    refine ⟨p j, ?_, by simp⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hj.2⟩

theorem dotProduct_permute [Fintype ι] [CommSemiring K] (p : Equiv.Perm ι) (x y : ι → K) :
    permute p x ⬝ᵥ permute p y = x ⬝ᵥ y := by
  simp only [dotProduct, permute_apply]
  exact Equiv.sum_comp p.symm (fun i => x i * y i)

/-! ### The dual code -/

/-- The dual code `{x | ∀ y ∈ C, ⟨x, y⟩ = 0}`. -/
def dual [Fintype ι] [CommRing K] (C : Submodule K (ι → K)) : Submodule K (ι → K) where
  carrier := {x | ∀ y ∈ C, x ⬝ᵥ y = 0}
  zero_mem' := fun y _ => zero_dotProduct y
  add_mem' := by
    intro x z hx hz y hy
    rw [add_dotProduct, hx y hy, hz y hy, add_zero]
  smul_mem' := by
    intro c x hx y hy
    rw [smul_dotProduct, hx y hy, smul_zero]

theorem mem_dual [Fintype ι] [CommRing K] {C : Submodule K (ι → K)} {x : ι → K} :
    x ∈ dual C ↔ ∀ y ∈ C, x ⬝ᵥ y = 0 :=
  Iff.rfl

/-- A code is self-dual if `C = C^⊥`. -/
def SelfDual [Fintype ι] [CommRing K] (C : Submodule K (ι → K)) : Prop :=
  C = dual C

theorem dual_map_permute [Fintype ι] [CommRing K] (C : Submodule K (ι → K)) (p : Equiv.Perm ι) :
    dual (C.map (permute p).toLinearMap) = (dual C).map (permute p).toLinearMap := by
  ext x
  simp only [mem_dual, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨permute p⁻¹ x, fun y hy => ?_, ?_⟩
    · have := h (permute p y) ⟨y, hy, rfl⟩
      rw [← dotProduct_permute p⁻¹, ← permute_mul, inv_mul_cancel, permute_one_apply] at this
      exact this
    · show permute p (permute p⁻¹ x) = x
      rw [← permute_mul, mul_inv_cancel, permute_one_apply]
  · rintro ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
    show permute p z ⬝ᵥ permute p w = 0
    rw [dotProduct_permute]
    exact hz w hw

theorem SelfDual.map_permute [Fintype ι] [CommRing K] {C : Submodule K (ι → K)} (hC : SelfDual C)
    (p : Equiv.Perm ι) : SelfDual (C.map (permute p).toLinearMap) := by
  unfold SelfDual at hC ⊢
  rw [dual_map_permute, ← hC]

/-- `dim C + dim C^⊥ = n`. -/
theorem finrank_add_finrank_dual [Fintype ι] [DecidableEq ι] [Field K] (C : Submodule K (ι → K)) :
    finrank K C + finrank K (dual C) = Fintype.card ι := by
  have h : dual C = (C.dualAnnihilator).map (dotProductEquiv K ι).symm.toLinearMap := by
    rw [← Submodule.comap_equiv_eq_map_symm]
    ext x
    simp only [mem_dual, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    rfl
  rw [h, LinearEquiv.finrank_map_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
    Module.finrank_fintype_fun_eq_card]

/-- A self-dual code has dimension `n / 2`. -/
theorem SelfDual.two_mul_finrank [Fintype ι] [DecidableEq ι] [Field K] {C : Submodule K (ι → K)}
    (hC : SelfDual C) : 2 * finrank K C = Fintype.card ι := by
  have h := finrank_add_finrank_dual C
  rw [← hC] at h
  omega

/-- Membership in `Aut C` only needs `C p ⊆ C` (finite length, coefficients in a field). -/
theorem mem_Aut_iff [Fintype ι] [Field K] {C : Submodule K (ι → K)} {p : Equiv.Perm ι} :
    p ∈ Aut C ↔ ∀ x ∈ C, permute p x ∈ C := by
  constructor
  · intro hp x hx
    exact permute_mem_of_mem_Aut hp hx
  · intro h
    rw [mem_Aut]
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    · exact LinearEquiv.finrank_map_eq (permute p) C

theorem mem_Aut_of_map_le [Fintype ι] [Field K] {C : Submodule K (ι → K)} {p : Equiv.Perm ι}
    (h : C.map (permute p).toLinearMap ≤ C) : p ∈ Aut C :=
  mem_Aut_iff.2 fun _ hx => h (Submodule.mem_map_of_mem hx)

/-- A self-orthogonal code of dimension `n / 2` is self-dual. -/
theorem selfDual_of_le_of_two_mul_finrank [Fintype ι] [DecidableEq ι] [Field K]
    {C : Submodule K (ι → K)} (hle : C ≤ dual C) (hdim : 2 * finrank K C = Fintype.card ι) :
    SelfDual C := by
  have h := finrank_add_finrank_dual C
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

/-- The dual of a span consists of the words orthogonal to the generators. -/
theorem mem_dual_span [Fintype ι] [CommRing K] {S : Set (ι → K)} {x : ι → K} :
    x ∈ dual (Submodule.span K S) ↔ ∀ y ∈ S, x ⬝ᵥ y = 0 := by
  constructor
  · intro h y hy
    exact h y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => exact dotProduct_zero x
    | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
    | smul a y _ hy => rw [dotProduct_smul, hy, smul_zero]

end General

/-! ## Binary codes -/

section Binary

variable {ι : Type*} [Fintype ι]

/-- A binary linear code of length `n`. -/
abbrev Code (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

/-- Type II: self-dual and doubly-even (every weight divisible by 4). -/
def TypeII (C : Submodule (ZMod 2) (ι → ZMod 2)) : Prop :=
  SelfDual C ∧ ∀ x ∈ C, 4 ∣ wt x

/-- Minimum weight at least `d`: every nonzero word has weight at least `d`. -/
def MinWt (C : Submodule (ZMod 2) (ι → ZMod 2)) (d : ℕ) : Prop :=
  ∀ x ∈ C, x ≠ 0 → d ≤ wt x

/-- A doubly-even self-dual `[72,36,16]` code: Type II of length 72 with minimum weight exactly 16. -/
def Ext72 (C : Code 72) : Prop :=
  TypeII C ∧ MinWt C 16 ∧ ∃ x ∈ C, wt x = 16

theorem TypeII.map_permute {C : Submodule (ZMod 2) (ι → ZMod 2)} (hC : TypeII C)
    (p : Equiv.Perm ι) : TypeII (C.map (permute p).toLinearMap) := by
  refine ⟨hC.1.map_permute p, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  show 4 ∣ wt (permute p x)
  rw [wt_permute]
  exact hC.2 x hx

theorem MinWt.map_permute {C : Submodule (ZMod 2) (ι → ZMod 2)} {d : ℕ} (hC : MinWt C d)
    (p : Equiv.Perm ι) : MinWt (C.map (permute p).toLinearMap) d := by
  rintro _ ⟨x, hx, rfl⟩ hne
  show d ≤ wt (permute p x)
  rw [wt_permute]
  refine hC x hx ?_
  rintro rfl
  exact hne (map_zero _)

theorem Ext72.map_permute {C : Code 72} (hC : Ext72 C) (p : Equiv.Perm (Fin 72)) :
    Ext72 (C.map (permute p).toLinearMap) := by
  obtain ⟨h1, h2, x, hx, hwx⟩ := hC
  exact ⟨h1.map_permute p, h2.map_permute p, permute p x, Submodule.mem_map_of_mem hx,
    by rw [wt_permute, hwx]⟩

/-- An extremal code of length 72 has dimension 36. -/
theorem Ext72.finrank {C : Code 72} (hC : Ext72 C) : finrank (ZMod 2) C = 36 := by
  have h := SelfDual.two_mul_finrank (K := ZMod 2) hC.1.1
  simp only [Fintype.card_fin] at h
  omega

end Binary

end C72
