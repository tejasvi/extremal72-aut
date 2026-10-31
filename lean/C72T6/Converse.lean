import C72T6.Gauge

/-!
# T6: the converse directions of Lemmas 3.2, 3.3 and 3.6, and Proposition 6.2 backward

For a self-dual `Y` and a bilinear form `B` on `Y`:
* Lemma 3.3 (b) backward: `B` symmetric ⇒ `C_B` self-dual (`CB_selfDual`);
* Lemma 3.3 (c) backward: (diag) for every `y` ⇒ `C_B` doubly-even (`CB_doublyEven`);
* Lemma 3.3 (d): `a = aStd` is an automorphism of `C_B` (`aStd_mem_CB`) and the contracted fixed code of `C_B` is `Y`
  (`Yof_CB`); with T4's `model` this is the converse of Lemma 3.2;
* Lemma 3.6 backward: if `Y` has minimum weight at least 8, `B ∈ A_0(Y)` and no constraint word has a bad syndrome, then
  `C_B` has minimum weight at least 16 (`minWt_CB`);
* Proposition 6.2 backward on the pair model (`prop62_converse`): a solution for `Y_k` gives a Type II code on
  `Fin 36 × 𝔽₂` with minimum weight at least 16, the automorphism `aStd`, and contracted fixed code `Y_k`. The minimum
  weight 8 of `Y_k` is a premise here: the code list is not rechecked in Lean.
-/

namespace C72.T6

open C72 C72.T4 Module Finset

variable {ι : Type*} [Fintype ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- The words `(x | x)`, `x ∈ Y`, lie in `C_B`. -/
theorem pv_self_mem_CB (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y) {x : ι → ZMod 2} (hx : x ∈ Y) :
    pv x x ∈ CB Y B := by
  refine mem_CB.2 ⟨0, x, fun y' => ?_, ?_⟩
  · rw [map_zero, LinearMap.zero_apply]
    exact dotProduct_eq_zero_of_selfDual hY hx y'.2
  · rw [Submodule.coe_zero, add_zero]

/-- For every `y ∈ Y` some word `(z | z + y)` lies in `C_B`. -/
theorem exists_mem_CB (B : LinearMap.BilinForm (ZMod 2) Y) (y : Y) :
    ∃ z : ι → ZMod 2, (∀ y' : Y, z ⬝ᵥ (y' : ι → ZMod 2) = B y y') ∧ pv z (z + y) ∈ CB Y B := by
  obtain ⟨z, hz⟩ := exists_dotProduct_eq (B y)
  exact ⟨z, hz, mem_CB.2 ⟨y, z, hz, rfl⟩⟩

/-- **Lemma 3.3 (b), backward.** If `B` is symmetric, `C_B` is self-dual. -/
theorem CB_selfDual (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y) (hsym : ∀ y y' : Y, B y y' = B y' y) :
    SelfDual (CB Y B) := by
  unfold SelfDual
  apply le_antisymm
  · intro c hc
    rw [mem_dual]
    intro c' hc'
    obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
    obtain ⟨y', z', hz', rfl⟩ := mem_CB.1 hc'
    have key : pv z (z + y) ⬝ᵥ pv z' (z' + y') = z ⬝ᵥ z' + (z ⬝ᵥ z' + z ⬝ᵥ (y' : ι → ZMod 2) +
        (y : ι → ZMod 2) ⬝ᵥ z' + (y : ι → ZMod 2) ⬝ᵥ (y' : ι → ZMod 2)) := by
      rw [dotProduct_pv, add_dotProduct, dotProduct_add, dotProduct_add]
      ring
    rw [key, hz y', dotProduct_comm (y : ι → ZMod 2) z', hz' y, dotProduct_eq_zero_of_selfDual hY y.2 y'.2,
      hsym y' y]
    generalize z ⬝ᵥ z' = a
    generalize B y y' = b
    revert a b
    decide
  · intro w hw
    obtain ⟨u, v, rfl⟩ := exists_pv w
    have hyY : u + v ∈ Y := by
      apply mem_of_mem_dual_of_selfDual hY
      intro x hx
      have h := (mem_dual.1 hw) (pv x x) (pv_self_mem_CB hY B hx)
      rw [dotProduct_pv, ← add_dotProduct] at h
      exact h
    refine mem_CB.2 ⟨⟨u + v, hyY⟩, u, fun y' => ?_, ?_⟩
    · obtain ⟨z', hz', hmem⟩ := exists_mem_CB B y'
      have h0 := (mem_dual.1 hw) _ hmem
      rw [dotProduct_pv, dotProduct_add] at h0
      have e1 : u ⬝ᵥ z' + v ⬝ᵥ z' = B ⟨u + v, hyY⟩ y' := by
        rw [← add_dotProduct, dotProduct_comm, hz' ⟨u + v, hyY⟩, hsym]
      have e2 : u ⬝ᵥ (y' : ι → ZMod 2) + v ⬝ᵥ (y' : ι → ZMod 2) = 0 := by
        rw [← add_dotProduct]
        exact dotProduct_eq_zero_of_selfDual hY hyY y'.2
      rw [← e1]
      revert e2 h0
      generalize u ⬝ᵥ z' = a
      generalize v ⬝ᵥ z' = b
      generalize v ⬝ᵥ (y' : ι → ZMod 2) = c
      generalize u ⬝ᵥ (y' : ι → ZMod 2) = d
      revert a b c d
      decide
    · congr 1
      funext i
      show v i = u i + (u i + v i)
      generalize u i = a
      generalize v i = b
      revert a b
      decide

/-- **Lemma 3.3 (c), backward.** If `B` satisfies (diag) for every `y ∈ Y`, then `C_B` is doubly-even. -/
theorem CB_doublyEven (hY : SelfDual Y) (h1 : allOnes ∈ Y) (B : LinearMap.BilinForm (ZMod 2) Y)
    (hdiag : ∀ y : Y, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, h1⟩) :
    ∀ c ∈ CB Y B, 4 ∣ wt c := by
  intro c hc
  obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
  rw [wt_pv_add]
  have ht : ((#(univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z i ≠ 0)) : ℕ) : ZMod 2) =
      B y ⟨allOnes, h1⟩ + B y y := by
    rw [← hz ⟨allOnes, h1⟩, ← hz y, Finset.card_filter, Nat.cast_sum, dotProduct, dotProduct,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [allOnes]
    rcases zmod2_cases ((y : ι → ZMod 2) i) with h | h <;>
      rcases zmod2_cases (z i) with h' | h' <;> simp [h, h', zmod2_add_self']
  rw [hdiag y] at ht
  have ht2 : ((#(univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z i ≠ 0)) : ℕ) : ZMod 2) =
      ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) := by
    rw [ht]
    generalize ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) = a
    generalize B y ⟨allOnes, h1⟩ = b
    revert a b
    decide
  rw [ZMod.natCast_eq_natCast_iff'] at ht2
  obtain ⟨m, hm⟩ := even_wt_of_mem_selfDual hY y.2
  rw [hm] at ht2 ⊢
  omega

/-- **Lemma 3.3 (d).** `a = aStd` is an automorphism of `C_B`. -/
theorem aStd_mem_CB (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y) :
    ∀ c ∈ CB Y B, permute aStd c ∈ CB Y B := by
  intro c hc
  obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
  rw [permute_aStd_pv]
  refine mem_CB.2 ⟨y, z + y, fun y' => ?_, ?_⟩
  · rw [add_dotProduct, hz y', dotProduct_eq_zero_of_selfDual hY y.2 y'.2, add_zero]
  · congr 1
    funext i
    simp only [Pi.add_apply]
    generalize z i = a
    generalize (y : ι → ZMod 2) i = b
    revert a b
    decide

/-- **Lemma 3.3 (d).** The contracted fixed code of `C_B` is `Y`. -/
theorem Yof_CB (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y) : Yof (CB Y B) = Y := by
  ext u
  rw [mem_Yof]
  constructor
  · intro h
    obtain ⟨y, z, hz, hzy⟩ := mem_CB.1 h
    obtain ⟨hu, hu'⟩ := pv_inj hzy
    have hy0 : y = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_zero]
      funext i
      have h2 := congrFun hu' i
      rw [hu] at h2
      simp only [Pi.add_apply, Pi.zero_apply] at h2 ⊢
      have key : ∀ a b : ZMod 2, a = a + b → b = 0 := by decide
      exact key _ _ h2
    apply mem_of_mem_dual_of_selfDual hY
    intro y' hy'
    rw [hu, hz ⟨y', hy'⟩, hy0, map_zero, LinearMap.zero_apply]
  · intro hu
    exact pv_self_mem_CB hY B hu

variable [DecidableEq ι]

/-- **Lemma 3.6, backward, with the small weights.** If `Y` has minimum weight at least 8, `B ∈ A_0(Y)`, and no
constraint word has a bad syndrome, then `C_B` has minimum weight at least 16. -/
theorem minWt_CB (hY : SelfDual Y) (h8 : MinWt Y 8) (h1 : allOnes ∈ Y) (B : LinearMap.BilinForm (ZMod 2) Y)
    (hA : InA0 Y h1 B) (hnr : ¬ RuledOut Y B) : MinWt (CB Y B) 16 := by
  intro c hc hc0
  have hdE := CB_doublyEven hY h1 B hA.2 c hc
  obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
  by_cases hy0 : y = 0
  · subst hy0
    have hzY : z ∈ Y := by
      apply mem_of_mem_dual_of_selfDual hY
      intro y' hy'
      rw [hz ⟨y', hy'⟩, map_zero, LinearMap.zero_apply]
    rw [Submodule.coe_zero, add_zero] at hc0 ⊢
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hc0 pv_zero
    have h := h8 z hzY hz0
    rw [wt_pv]
    omega
  · have hy0' : (y : ι → ZMod 2) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hwy := h8 y y.2 hy0'
    obtain ⟨m, hm⟩ := even_wt_of_mem_selfDual hY y.2
    rw [wt_pv_add] at hdE ⊢
    by_contra hlt
    rw [not_le] at hlt
    apply hnr
    refine ⟨y, ?_, univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z i ≠ 0), ?_, ?_, ?_⟩
    · unfold IsConstraint
      omega
    · intro i hi
      exact (Finset.mem_filter.1 hi).2.1
    · omega
    · intro x hx
      rw [← hz x, dotProduct, dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [indicator, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx i with h | h
      · rcases zmod2_cases (z i) with h' | h' <;> simp [h, h']
      · simp [h]

/-- **Proposition 6.2, backward (pair model).** A solution for `Y_k` (a form of `A_0(Y_k)` that is not ruled out) gives a
Type II code on `Fin 36 × 𝔽₂` with minimum weight at least 16, the automorphism `aStd`, and contracted fixed code `Y_k`,
provided `Y_k` has minimum weight at least 8 (a property of the code list, not rechecked in Lean). -/
theorem prop62_converse (k : Fin 41) (B : LinearMap.BilinForm (ZMod 2) (Yc k)) (hA : InA0 (Yc k) (allOnes_mem_Yc k) B)
    (hnr : ¬ RuledOut (Yc k) B) (h8 : MinWt (Yc k) 8) :
    TypeII (CB (Yc k) B) ∧ MinWt (CB (Yc k) B) 16 ∧ (∀ c ∈ CB (Yc k) B, permute aStd c ∈ CB (Yc k) B) ∧
      Yof (CB (Yc k) B) = Yc k :=
  ⟨⟨CB_selfDual (Yc_selfDual k) B hA.1, CB_doublyEven (Yc_selfDual k) (allOnes_mem_Yc k) B hA.2⟩,
    minWt_CB (Yc_selfDual k) h8 (allOnes_mem_Yc k) B hA hnr, aStd_mem_CB (Yc_selfDual k) B,
    Yof_CB (Yc_selfDual k) B⟩

end C72.T6
