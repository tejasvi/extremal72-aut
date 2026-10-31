import C72T4.Model

/-!
# T4: Lemma 3.2 and the forward directions of Lemma 3.3 (b), (c)

Let `C` be a Type II code on the pairs `ι × 𝔽₂`, invariant under `aStd`, whose contracted fixed code `Y` is
self-dual. Then `C = C_B` for a bilinear form `B` on `Y` (Lemma 3.2), `B` is symmetric (Lemma 3.3 (b), the direction
"`C_B` self-dual ⇒ `B` symmetric") and `B` satisfies condition (diag) for every `y ∈ Y` (Lemma 3.3 (c), the direction
"`C_B` doubly-even ⇒ (diag)").

The paper takes `σ(C) = Y` from (L2) (freeness). Here it follows from the self-duality of `Y` by duality
(`Yof_le_map_sigmaL`); this is what Lemma 3.2 takes from freeness.
-/

namespace C72.T4

open C72 Module Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_of_mem_dual_of_selfDual {κ : Type*} [Fintype κ] {Y : Submodule (ZMod 2) (κ → ZMod 2)}
    (hY : SelfDual Y) {x : κ → ZMod 2} (h : x ∈ dual Y) : x ∈ Y :=
  (SetLike.ext_iff.1 hY x).2 h

theorem mem_dual_of_mem_of_selfDual {κ : Type*} [Fintype κ] {Y : Submodule (ZMod 2) (κ → ZMod 2)}
    (hY : SelfDual Y) {x : κ → ZMod 2} (h : x ∈ Y) : x ∈ dual Y :=
  (SetLike.ext_iff.1 hY x).1 h

theorem dotProduct_eq_zero_of_selfDual {κ : Type*} [Fintype κ] {Y : Submodule (ZMod 2) (κ → ZMod 2)}
    (hY : SelfDual Y) {x x' : κ → ZMod 2} (hx : x ∈ Y) (hx' : x' ∈ Y) : x ⬝ᵥ x' = 0 :=
  (mem_dual.1 (mem_dual_of_mem_of_selfDual hY hx)) x' hx'

omit [Fintype ι] [DecidableEq ι] in
theorem exists_pv (c : ι × ZMod 2 → ZMod 2) : ∃ u v, c = pv u v :=
  ⟨fstH c, sndH c, (pv_fstH_sndH c).symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem sigmaL_pv (u v : ι → ZMod 2) : sigmaL (pv u v) = u + v :=
  rfl

/-- `fstH` as a linear map. -/
def fstHL : (ι × ZMod 2 → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i => (i, 0))

omit [Fintype ι] [DecidableEq ι] in
theorem fstHL_apply (c : ι × ZMod 2 → ZMod 2) : fstHL c = fstH c :=
  rfl

/-- In `𝔽₂`: from `x + y = 0` follows `y = x`. -/
theorem zmod2_eq_of_add_eq_zero : ∀ x y : ZMod 2, x + y = 0 → y = x := by
  decide

/-- In `𝔽₂`: from `a + (a + b + c + 0) = 0` follows `b = c`. -/
theorem zmod2_cancel_aux : ∀ a b c : ZMod 2, a + (a + b + c + 0) = 0 → b = c := by
  decide

/-- In `𝔽₂`: `x + y = w` gives `x = w + y`. -/
theorem zmod2_eq_add_of_add_eq : ∀ x y w : ZMod 2, x + y = w → x = w + y := by
  decide

omit [Fintype ι] [DecidableEq ι] in
theorem vec_eq_of_add_eq_zero {u v : ι → ZMod 2} (h : u + v = 0) : v = u := by
  funext i
  exact zmod2_eq_of_add_eq_zero (u i) (v i) (congrFun h i)

section Model

variable {C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)}

omit [Fintype ι] [DecidableEq ι] in
/-- `c + c a = (u + v | u + v)`, so `σ c ∈ Y` for `c ∈ C`. -/
theorem sigmaL_mem_Yof (ha : ∀ c ∈ C, permute aStd c ∈ C) {c : ι × ZMod 2 → ZMod 2} (hc : c ∈ C) :
    sigmaL c ∈ Yof C := by
  obtain ⟨u, v, rfl⟩ := exists_pv c
  rw [mem_Yof, sigmaL_pv]
  have h : pv (u + v) (u + v) = pv u v + permute aStd (pv u v) := by
    rw [permute_aStd_pv, pv_add, add_comm v u]
  rw [h]
  exact C.add_mem hc (ha _ hc)

/-- If `C` and `Y` are self-dual, then `Y ⊆ σ(C)`: a word orthogonal to `σ(C)` gives a word `(w | w)` orthogonal
to `C`. -/
theorem Yof_le_map_sigmaL (hC : SelfDual C) (hY : SelfDual (Yof C)) : Yof C ≤ C.map sigmaL := by
  have h1 : dual (C.map sigmaL) ≤ Yof C := by
    intro w hw
    rw [mem_Yof]
    apply mem_of_mem_dual_of_selfDual hC
    rw [mem_dual]
    intro c hc
    obtain ⟨u, v, rfl⟩ := exists_pv c
    rw [dotProduct_pv, ← dotProduct_add]
    exact (mem_dual.1 hw) (sigmaL (pv u v)) (Submodule.mem_map_of_mem hc)
  calc Yof C = dual (Yof C) := hY
    _ ≤ dual (dual (C.map sigmaL)) := dual_antitone h1
    _ = C.map sigmaL := dual_dual _

/-- `σ` restricted to `C`, with values in `Y`. -/
def sigmaR (ha : ∀ c ∈ C, permute aStd c ∈ C) : C →ₗ[ZMod 2] Yof C :=
  LinearMap.codRestrict (Yof C) (sigmaL ∘ₗ C.subtype) (fun c => sigmaL_mem_Yof ha c.2)

theorem sigmaR_range (ha : ∀ c ∈ C, permute aStd c ∈ C) (hC : SelfDual C) (hY : SelfDual (Yof C)) :
    LinearMap.range (sigmaR ha) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨c, hc, hcy⟩ := Submodule.mem_map.1 (Yof_le_map_sigmaL hC hY y.2)
  exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩

/-- **Lemma 3.2 with Lemma 3.3 (b), (c) forward.** If `C` is Type II, invariant under `aStd`, and its contracted fixed
code `Y` is self-dual, then `C = C_B` for a bilinear form `B` on `Y` that is symmetric and satisfies (diag)
`B(y, y) = |y|/2 + B(y, 𝟙)` for every `y ∈ Y`. -/
theorem model {Y : Submodule (ZMod 2) (ι → ZMod 2)} (hYC : Yof C = Y) (hC : TypeII C)
    (ha : ∀ c ∈ C, permute aStd c ∈ C) (hY : SelfDual Y) :
    ∃ B : LinearMap.BilinForm (ZMod 2) Y, CB Y B = C ∧ (∀ y y' : Y, B y y' = B y' y) ∧
      ∀ y : Y, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, allOnes_mem_of_selfDual hY⟩ := by
  subst hYC
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (sigmaR ha) (sigmaR_range ha hC.1 hY)
  let z0 : Yof C →ₗ[ZMod 2] (ι → ZMod 2) := fstHL ∘ₗ C.subtype ∘ₗ s
  have hz0 : ∀ y, z0 y = fstH (s y : ι × ZMod 2 → ZMod 2) := fun y => rfl
  have hsig : ∀ y : Yof C, sigmaL (s y : ι × ZMod 2 → ZMod 2) = (y : ι → ZMod 2) := by
    intro y
    have := LinearMap.congr_fun hs y
    exact congrArg Subtype.val this
  have hsy : ∀ y : Yof C, (s y : ι × ZMod 2 → ZMod 2) = pv (z0 y) (z0 y + y) := by
    intro y
    have h1 := hsig y
    rw [hz0]
    conv_lhs => rw [← pv_fstH_sndH (s y : ι × ZMod 2 → ZMod 2)]
    congr 1
    rw [sigmaL_apply] at h1
    have h2 : fstH (s y : ι × ZMod 2 → ZMod 2) + (fstH (s y : ι × ZMod 2 → ZMod 2) + sndH (s y : _))
        = fstH (s y : ι × ZMod 2 → ZMod 2) + (y : ι → ZMod 2) := by rw [h1]
    rw [← add_assoc, C72.vec_add_self, zero_add] at h2
    exact h2
  let B : LinearMap.BilinForm (ZMod 2) (Yof C) :=
    LinearMap.mk₂ (ZMod 2) (fun y y' => z0 y ⬝ᵥ (y' : ι → ZMod 2))
      (fun y₁ y₂ y' => by rw [map_add, add_dotProduct])
      (fun a y y' => by rw [map_smul, smul_dotProduct])
      (fun y y₁ y₂ => by rw [Submodule.coe_add, dotProduct_add])
      (fun a y y' => by rw [Submodule.coe_smul, dotProduct_smul])
  have hB : ∀ y y', B y y' = z0 y ⬝ᵥ (y' : ι → ZMod 2) := fun y y' => rfl
  refine ⟨B, ?_, ?_, ?_⟩
  · -- `C_B = C`
    apply le_antisymm
    · intro c hc
      obtain ⟨y, z, hz, rfl⟩ := mem_CB.1 hc
      have hx : z + z0 y ∈ Yof C := by
        apply mem_of_mem_dual_of_selfDual hY
        intro y' hy'
        rw [add_dotProduct, hz ⟨y', hy'⟩, hB, zmod2_add_self']
      have hc' : pv z (z + y) = (s y : ι × ZMod 2 → ZMod 2) + pv (z + z0 y) (z + z0 y) := by
        rw [hsy, pv_add]
        congr 1
        · funext i
          simp only [Pi.add_apply]
          generalize z i = a
          generalize z0 y i = b
          revert a b
          decide
        · funext i
          simp only [Pi.add_apply]
          generalize z i = a
          generalize z0 y i = b
          generalize (y : ι → ZMod 2) i = d
          revert a b d
          decide
      rw [hc']
      exact C.add_mem (s y).2 hx
    · intro c hc
      obtain ⟨u, v, rfl⟩ := exists_pv c
      let y : Yof C := sigmaR ha ⟨pv u v, hc⟩
      have hyc : (y : ι → ZMod 2) = u + v := rfl
      have hd : pv u v + (s y : ι × ZMod 2 → ZMod 2) ∈ C := C.add_mem hc (s y).2
      rw [hsy, pv_add] at hd
      have hvu : v + (z0 y + y) = u + z0 y := by
        have h1 : (u + z0 y) + (v + (z0 y + y)) = 0 := by
          rw [hyc]
          funext i
          simp only [Pi.add_apply, Pi.zero_apply]
          generalize u i = a
          generalize v i = b
          generalize (z0 y) i = d
          revert a b d
          decide
        exact vec_eq_of_add_eq_zero h1
      rw [hvu] at hd
      have hxY : u + z0 y ∈ Yof C := hd
      refine mem_CB.2 ⟨y, u, fun y' => ?_, ?_⟩
      · have h0 := dotProduct_eq_zero_of_selfDual hY hxY y'.2
        rw [add_dotProduct] at h0
        rw [hB]
        exact (zmod2_eq_of_add_eq_zero _ _ h0).symm
      · congr 1
        rw [hyc]
        funext i
        simp only [Pi.add_apply]
        generalize u i = a
        generalize v i = b
        revert a b
        decide
  · -- `B` is symmetric
    intro y y'
    have h0 := (mem_dual.1 (mem_dual_of_mem_of_selfDual hC.1 (s y).2)) (s y' : ι × ZMod 2 → ZMod 2) (s y').2
    have key : (s y : ι × ZMod 2 → ZMod 2) ⬝ᵥ (s y' : ι × ZMod 2 → ZMod 2) =
        z0 y ⬝ᵥ z0 y' + (z0 y ⬝ᵥ z0 y' + z0 y ⬝ᵥ (y' : ι → ZMod 2) + (y : ι → ZMod 2) ⬝ᵥ z0 y' +
          (y : ι → ZMod 2) ⬝ᵥ (y' : ι → ZMod 2)) := by
      rw [hsy, hsy, dotProduct_pv, add_dotProduct, dotProduct_add, dotProduct_add]
      ring
    rw [key, dotProduct_eq_zero_of_selfDual hY y.2 y'.2] at h0
    rw [hB, hB, dotProduct_comm (z0 y')]
    exact zmod2_cancel_aux _ _ _ h0
  · -- condition (diag)
    intro y
    have h4 : 4 ∣ wt (y : ι → ZMod 2) +
        2 * #(univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z0 y i ≠ 0)) := by
      have := hC.2 _ (s y).2
      rw [hsy, wt_pv_add] at this
      exact this
    have hev : Even (wt (y : ι → ZMod 2)) := even_wt_of_mem_selfDual hY y.2
    have hpar : ((wt (y : ι → ZMod 2) / 2 +
        #(univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z0 y i ≠ 0)) : ℕ) : ZMod 2) = 0 := by
      rw [ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
      obtain ⟨m, hm⟩ := hev
      rw [hm] at h4 ⊢
      omega
    have htB : ((#(univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ z0 y i ≠ 0)) : ℕ) : ZMod 2) =
        B y y + B y ⟨allOnes, allOnes_mem_of_selfDual hY⟩ := by
      rw [hB, hB, Finset.card_filter, Nat.cast_sum, dotProduct, dotProduct, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [allOnes]
      rcases zmod2_cases ((y : ι → ZMod 2) i) with h1 | h1 <;>
        rcases zmod2_cases (z0 y i) with h2 | h2 <;> simp [h1, h2, zmod2_add_self']
    rw [Nat.cast_add, htB] at hpar
    exact zmod2_eq_add_of_add_eq _ _ _ (zmod2_eq_of_add_eq_zero _ _ hpar)

end Model

end C72.T4
