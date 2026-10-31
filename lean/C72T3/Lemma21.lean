import C72T3.Decomp5
import C72T3.Hyp

/-!
# T3: Lemma 2.1 (`C₀ = e8 ⊕ e8`) from the named hypothesis `H_16`

For an extremal code `C` with `g5 ∈ Aut C`:

* `|φ₀(a, x)| = 5|a| + |x|` (`wt_phi0`), so `C₀` is doubly-even, self-dual (`C0_typeII`) and has minimum
  weight 4 (`C0_minWt`); no word of weight 4 of `C₀` contains both fixed points 14 and 15 (`C0_no_w4_both`).
* `H_16` gives `C₀ ≃ e8 ⊕ e8` or `C₀ ≃ d₁₆⁺`. In `d₁₆⁺` every two coordinates lie in a word of weight 4, so the
  second case is impossible (`not_permEquiv_d16plus`). In `e8 ⊕ e8` the images of 14 and 15 lie in different
  halves, and the translations of `AG(3, 2)` (`Aut e8` is transitive) move them to the fixed-point coordinates.
* **Lemma 2.1** (`lemma21_C0`): a permutation of `Fin 16` that maps `{14, 15}` onto itself (a permutation of the
  cycles and of the fixed points) maps `C₀` onto `e8e8w`, the layout of Sec. 2.2.
* `lemma21`: the same permutation, lifted to the 72 coordinates (`liftP`, which commutes with `g5`), turns `C`
  into an equivalent extremal code `C P` with `g5 ∈ Aut (C P)` and `C₀(C P) = e8e8w`.
-/

namespace C72.T3

open Equiv Equiv.Perm Finset Module

variable {C : Code 72}

/-! ## Weights of `φ₀u` -/

/-- `|a|`: the number of cycles on which `u` is nonzero. -/
def wtCyc (u : Fin 16 → ZMod 2) : ℕ :=
  ∑ a : Fin 14, if u (Fin.castAdd 2 a) = 0 then 0 else 1

/-- `|x|`: the number of fixed points on which `u` is nonzero. -/
def wtFix (u : Fin 16 → ZMod 2) : ℕ :=
  ∑ x : Fin 2, if u (Fin.natAdd 14 x) = 0 then 0 else 1

theorem wt_C0_eq (u : Fin 16 → ZMod 2) : wt u = wtCyc u + wtFix u := by
  rw [wt_eq_sum, sum_fin16]
  rfl

theorem wt_const5 : ∀ s : ZMod 2, wt (fun _ : Fin 5 => s) = if s = 0 then 0 else 5 := by decide +kernel

/-- `|φ₀(a, x)| = 5|a| + |x|` (Sec. 2.1). -/
theorem wt_phi0 (u : Fin 16 → ZMod 2) : wt (phi0 u) = 5 * wtCyc u + wtFix u := by
  have h := wt_phi0_add_phi1 u 0
  rw [map_zero, add_zero] at h
  have h2 : ∑ a : Fin 14, wt (fun b => u (Fin.castAdd 2 a) + psi ((0 : Fin 14 → F16) a) b) =
      5 * wtCyc u := by
    rw [wtCyc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Pi.zero_apply, psi_zero, add_zero, wt_const5]
    split_ifs <;> rfl
  rw [h, h2]
  rfl

theorem wtFix_le (u : Fin 16 → ZMod 2) : wtFix u ≤ 2 := by
  rw [wtFix, Fin.sum_univ_two]
  split_ifs <;> omega

/-- `C₀` is doubly-even: `|u| = |a| + |x| ≡ 5|a| + |x| = |φ₀u| ≡ 0 (mod 4)`. -/
theorem C0_doublyEven (hC : TypeII C) {u : Fin 16 → ZMod 2} (hu : u ∈ C0 C) : 4 ∣ wt u := by
  have h := hC.2 _ hu
  rw [wt_phi0] at h
  rw [wt_C0_eq]
  omega

theorem C0_typeII (hC : Ext72 C) (hg : g5 ∈ Aut C) : TypeII (C0 C) :=
  ⟨selfDual_C0 hC.1.1 hg, fun _ hu => C0_doublyEven hC.1 hu⟩

theorem phi0_ne_zero {u : Fin 16 → ZMod 2} (hu : u ≠ 0) : phi0 u ≠ 0 :=
  fun h => hu (phi0_injective (h.trans (map_zero phi0).symm))

/-- `C₀` has minimum weight 4: `5|a| + |x| ≥ 16` and `|x| ≤ 2` give `|a| ≥ 3`. -/
theorem C0_minWt (hC : Ext72 C) : MinWt (C0 C) 4 := by
  intro u hu hne
  have h16 := hC.2.1 _ hu (phi0_ne_zero hne)
  rw [wt_phi0] at h16
  have hde := C0_doublyEven hC.1 hu
  rw [wt_C0_eq] at hde ⊢
  have hfix := wtFix_le u
  omega

/-- No word of weight 4 of `C₀` contains both fixed points 14 and 15: it would have `|a| = |x| = 2`, and
`|φ₀u| = 12 < 16`. -/
theorem C0_no_w4_both (hC : Ext72 C) {u : Fin 16 → ZMod 2} (hu : u ∈ C0 C) (hw : wt u = 4)
    (h14 : u 14 ≠ 0) (h15 : u 15 ≠ 0) : False := by
  have hne : u ≠ 0 := by
    rintro rfl
    rw [wt_zero'] at hw
    exact absurd hw (by norm_num)
  have h16 := hC.2.1 _ hu (phi0_ne_zero hne)
  rw [wt_phi0] at h16
  rw [wt_C0_eq] at hw
  have hfix : wtFix u = 2 := by
    have e0 : (Fin.natAdd 14 (0 : Fin 2) : Fin 16) = 14 := rfl
    have e1 : (Fin.natAdd 14 (1 : Fin 2) : Fin 16) = 15 := rfl
    rw [wtFix, Fin.sum_univ_two, e0, e1]
    simp [h14, h15]
  omega

/-! ## Excluding `d₁₆⁺`, placing the fixed points in `e8 ⊕ e8` -/

theorem perm_inv_apply_mem {D X : Code 16} {p : Perm (Fin 16)} (hp : D.map (permute p).toLinearMap = X)
    {w : Fin 16 → ZMod 2} (hw : w ∈ X) : permute p⁻¹ w ∈ D := by
  rw [← hp, mem_map_permute_iff] at hw
  exact hw

theorem ne_14_15 (p : Perm (Fin 16)) : p 14 ≠ p 15 :=
  fun h => absurd (p.injective h) (by decide)

/-- `C₀` is not equivalent to `d₁₆⁺`: there the coordinates `p 14` and `p 15` lie in a word of weight 4. -/
theorem not_permEquiv_d16plus (hC : Ext72 C) : ¬ PermEquiv (C0 C) d16plus := by
  rintro ⟨p, hp⟩
  obtain ⟨w, hw, hw4, hj, hk⟩ := d16plus_pair (p 14) (p 15) (ne_14_15 p)
  have hu := perm_inv_apply_mem hp hw
  apply C0_no_w4_both hC hu
  · rw [wt_permute, hw4]
  · rw [permute_inv_apply, hj]
    exact one_ne_zero
  · rw [permute_inv_apply, hk]
    exact one_ne_zero

/-- If `C₀ p = e8 ⊕ e8`, then `p 14` and `p 15` lie in different halves. -/
theorem halves_differ (hC : Ext72 C) {p : Perm (Fin 16)} (hp : (C0 C).map (permute p).toLinearMap = e8e8) :
    ¬ ((p 14).val < 8 ↔ (p 15).val < 8) := by
  intro hsame
  obtain ⟨w, hw, hw4, hj, hk⟩ := e8e8_pair (p 14) (p 15) (ne_14_15 p) hsame
  have hu := perm_inv_apply_mem hp hw
  apply C0_no_w4_both hC hu
  · rw [wt_permute, hw4]
  · rw [permute_inv_apply, hj]
    exact one_ne_zero
  · rw [permute_inv_apply, hk]
    exact one_ne_zero

/-- **Lemma 2.1, `e8 ⊕ e8` case**: a permutation of `Fin 16` mapping `{14, 15}` onto itself maps `C₀` onto
`e8e8w`. -/
theorem exists_good_perm (hC : Ext72 C) {p : Perm (Fin 16)}
    (hp : (C0 C).map (permute p).toLinearMap = e8e8) :
    ∃ p' : Perm (Fin 16), (C0 C).map (permute p').toLinearMap = e8e8w ∧
      (p' 14 = 14 ∨ p' 14 = 15) ∧ (p' 15 = 14 ∨ p' 15 = 15) := by
  have hdiff := halves_differ hC hp
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 8, (p 14 = Fin.castAdd 8 a ∧ p 15 = Fin.natAdd 8 b) ∨
      (p 15 = Fin.castAdd 8 a ∧ p 14 = Fin.natAdd 8 b) := by
    by_cases h : (p 14).val < 8
    · have h' : ¬ (p 15).val < 8 := fun h' => hdiff ⟨fun _ => h', fun _ => h⟩
      refine ⟨⟨(p 14).val, h⟩, ⟨(p 15).val - 8, by omega⟩, Or.inl ⟨Fin.ext rfl, Fin.ext ?_⟩⟩
      simp only [Fin.val_natAdd]
      omega
    · have h' : (p 15).val < 8 := by
        by_contra h'
        exact hdiff ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
      refine ⟨⟨(p 15).val, h'⟩, ⟨(p 14).val - 8, by omega⟩, Or.inr ⟨Fin.ext rfl, Fin.ext ?_⟩⟩
      simp only [Fin.val_natAdd]
      omega
  obtain ⟨q, hq, hqa, hqb⟩ : ∃ q : Perm (Fin 16), q ∈ Aut e8e8 ∧ q (Fin.castAdd 8 a) = 7 ∧
      q (Fin.natAdd 8 b) = 15 := by
    refine ⟨sumPerm (tauP a) (tauP b), sumPerm_mem_Aut (tauP_mem_Aut a) (tauP_mem_Aut b), ?_, ?_⟩
    · rw [sumPerm_castAdd, tauP_apply_self]
      rfl
    · rw [sumPerm_natAdd, tauP_apply_self]
      rfl
  refine ⟨rho * q * p, ?_, ?_, ?_⟩
  · rw [map_permute_mul, map_permute_mul, hp, mem_Aut.1 hq]
    rfl
  · rcases hab with ⟨h1, _⟩ | ⟨_, h2⟩
    · left
      rw [Perm.mul_apply, Perm.mul_apply, h1, hqa]
      rfl
    · right
      rw [Perm.mul_apply, Perm.mul_apply, h2, hqb]
      rfl
  · rcases hab with ⟨_, h2⟩ | ⟨h1, _⟩
    · right
      rw [Perm.mul_apply, Perm.mul_apply, h2, hqb]
      rfl
    · left
      rw [Perm.mul_apply, Perm.mul_apply, h1, hqa]
      rfl

/-- **Lemma 2.1** [FN12, Lemma 5.1], from `H_16`: up to a permutation of the cycles and of the fixed points
(a permutation of `Fin 16` that maps `{14, 15}` onto itself), `C₀ = e8 ⊕ e8` with one fixed point in each
component, in the layout of Sec. 2.2 (`e8e8w`). -/
theorem lemma21_C0 (h16 : H_16) (hC : Ext72 C) (hg : g5 ∈ Aut C) :
    ∃ p' : Perm (Fin 16), (p' 14 = 14 ∨ p' 14 = 15) ∧ (p' 15 = 14 ∨ p' 15 = 15) ∧
      (C0 C).map (permute p').toLinearMap = e8e8w := by
  rcases h16 (C0 C) (C0_typeII hC hg) with ⟨p, hp⟩ | hd
  · obtain ⟨p', hp', h14, h15⟩ := exists_good_perm hC hp
    exact ⟨p', h14, h15, hp'⟩
  · exact absurd hd (not_permEquiv_d16plus hC)

/-! ## Lifting a permutation of the cycles and fixed points to the 72 coordinates -/

/-- A permutation of `Fin 16` that maps `{14, 15}` onto itself permutes the cycles `0, …, 13` (by `σ`) and the
fixed points (by `τ`). -/
theorem exists_sigma_tau {p' : Perm (Fin 16)} (h14 : p' 14 = 14 ∨ p' 14 = 15)
    (h15 : p' 15 = 14 ∨ p' 15 = 15) :
    ∃ (σ : Perm (Fin 14)) (τ : Perm (Fin 2)), (∀ a, p' (Fin.castAdd 2 a) = Fin.castAdd 2 (σ a)) ∧
      ∀ x, p' (Fin.natAdd 14 x) = Fin.natAdd 14 (τ x) := by
  have v14 : (p' 14).val = 14 ∨ (p' 14).val = 15 := by
    rcases h14 with h | h <;> rw [h] <;> decide
  have v15 : (p' 15).val = 14 ∨ (p' 15).val = 15 := by
    rcases h15 with h | h <;> rw [h] <;> decide
  have vne : (p' 14).val ≠ (p' 15).val := fun h => ne_14_15 p' (Fin.ext h)
  have hlt : ∀ a : Fin 14, (p' (Fin.castAdd 2 a)).val < 14 := by
    intro a
    by_contra hge
    have hy := (p' (Fin.castAdd 2 a)).isLt
    have ha := a.isLt
    have hcases : (p' (Fin.castAdd 2 a)).val = (p' 14).val ∨
        (p' (Fin.castAdd 2 a)).val = (p' 15).val := by omega
    rcases hcases with h | h
    · have h' := congrArg Fin.val (p'.injective (Fin.ext h))
      simp only [Fin.val_castAdd] at h'
      have : ((14 : Fin 16) : ℕ) = 14 := rfl
      omega
    · have h' := congrArg Fin.val (p'.injective (Fin.ext h))
      simp only [Fin.val_castAdd] at h'
      have : ((15 : Fin 16) : ℕ) = 15 := rfl
      omega
  have hge : ∀ x : Fin 2, 14 ≤ (p' (Fin.natAdd 14 x)).val := by
    intro x
    fin_cases x
    · show 14 ≤ (p' 14).val
      omega
    · show 14 ≤ (p' 15).val
      omega
  let σf : Fin 14 → Fin 14 := fun a => ⟨(p' (Fin.castAdd 2 a)).val, hlt a⟩
  have hσinj : Function.Injective σf := by
    intro a a' h
    have h0 : (σf a).val = (σf a').val := congrArg Fin.val h
    have h' : (p' (Fin.castAdd 2 a)).val = (p' (Fin.castAdd 2 a')).val := h0
    have h'' := congrArg Fin.val (p'.injective (Fin.ext h'))
    simp only [Fin.val_castAdd] at h''
    exact Fin.ext h''
  let τf : Fin 2 → Fin 2 := fun x => ⟨(p' (Fin.natAdd 14 x)).val - 14, by
    have := (p' (Fin.natAdd 14 x)).isLt
    omega⟩
  have hτinj : Function.Injective τf := by
    intro x x' h
    have h0 : (τf x).val = (τf x').val := congrArg Fin.val h
    have h' : (p' (Fin.natAdd 14 x)).val - 14 = (p' (Fin.natAdd 14 x')).val - 14 := h0
    have hx := hge x
    have hx' := hge x'
    have h'' := congrArg Fin.val (p'.injective (Fin.ext (by omega :
      (p' (Fin.natAdd 14 x)).val = (p' (Fin.natAdd 14 x')).val)))
    simp only [Fin.val_natAdd] at h''
    exact Fin.ext (by omega)
  refine ⟨Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj),
    Equiv.ofBijective τf (Finite.injective_iff_bijective.1 hτinj), ?_, ?_⟩
  · intro a
    apply Fin.ext
    simp [σf]
  · intro x
    apply Fin.ext
    have hx := hge x
    simp only [Equiv.ofBijective_apply, Fin.val_natAdd, τf]
    omega

/-- The permutation of the cycles (by `σ`) and of the fixed points (by `τ`) on the 72 coordinates:
`(a, b) ↦ (σ a, b)`, `inr x ↦ inr (τ x)`. -/
def liftP (σ : Perm (Fin 14)) (τ : Perm (Fin 2)) : Perm (Fin 72) :=
  E72.permCongr (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl (Fin 5))) τ)

theorem liftP_E72 (σ : Perm (Fin 14)) (τ : Perm (Fin 2)) (z : Z) :
    liftP σ τ (E72 z) = E72 (Equiv.sumCongr (Equiv.prodCongr σ (Equiv.refl (Fin 5))) τ z) := by
  rw [liftP, Equiv.permCongr_apply, Equiv.symm_apply_apply]

/-- `liftP σ τ` commutes with `g5`: it permutes whole cycles and fixes the position inside each cycle. -/
theorem liftP_comm (σ : Perm (Fin 14)) (τ : Perm (Fin 2)) : liftP σ τ * g5 = g5 * liftP σ τ := by
  ext i
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [Perm.mul_apply, Perm.mul_apply, g5_E72, liftP_E72, liftP_E72, g5_E72]
  rcases z with ⟨a, b⟩ | x <;> rfl

theorem permute_liftP_inv_phi0 {p' : Perm (Fin 16)} {σ : Perm (Fin 14)} {τ : Perm (Fin 2)}
    (hσ : ∀ a, p' (Fin.castAdd 2 a) = Fin.castAdd 2 (σ a))
    (hτ : ∀ x, p' (Fin.natAdd 14 x) = Fin.natAdd 14 (τ x)) (u : Fin 16 → ZMod 2) :
    permute (liftP σ τ)⁻¹ (phi0 u) = phi0 (permute p'⁻¹ u) := by
  funext i
  obtain ⟨z, rfl⟩ := E72.surjective i
  rw [permute_inv_apply, liftP_E72, phi0_E72, phi0_E72, permute_inv_apply]
  rcases z with ⟨a, b⟩ | x
  · show u (Fin.castAdd 2 (σ a)) = u (p' (Fin.castAdd 2 a))
    rw [hσ]
  · show u (Fin.natAdd 14 (τ x)) = u (p' (Fin.natAdd 14 x))
    rw [hτ]

theorem C0_map_liftP {p' : Perm (Fin 16)} {σ : Perm (Fin 14)} {τ : Perm (Fin 2)}
    (hσ : ∀ a, p' (Fin.castAdd 2 a) = Fin.castAdd 2 (σ a))
    (hτ : ∀ x, p' (Fin.natAdd 14 x) = Fin.natAdd 14 (τ x)) (C : Code 72) :
    C0 (C.map (permute (liftP σ τ)).toLinearMap) = (C0 C).map (permute p').toLinearMap := by
  ext u
  rw [mem_C0, mem_map_permute_iff, mem_map_permute_iff, mem_C0, permute_liftP_inv_phi0 hσ hτ]

/-- **Lemma 2.1, relabelling form.** After a relabelling `P` of the coordinates that permutes the cycles and the
fixed points, the code `C P` is extremal, `g5 ∈ Aut (C P)`, and its fixed code is exactly `e8e8w`. -/
theorem lemma21 (h16 : H_16) (hC : Ext72 C) (hg : g5 ∈ Aut C) :
    ∃ P : Perm (Fin 72), Ext72 (C.map (permute P).toLinearMap) ∧ g5 ∈ Aut (C.map (permute P).toLinearMap) ∧
      C0 (C.map (permute P).toLinearMap) = e8e8w := by
  obtain ⟨p', h14, h15, hp'⟩ := lemma21_C0 h16 hC hg
  obtain ⟨σ, τ, hσ, hτ⟩ := exists_sigma_tau h14 h15
  refine ⟨liftP σ τ, hC.map_permute _, ?_, ?_⟩
  · rw [mem_Aut_map_permute_iff]
    have h : (liftP σ τ)⁻¹ * g5 * liftP σ τ = g5 := by
      rw [mul_assoc, ← liftP_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h]
    exact hg
  · rw [C0_map_liftP hσ hτ, hp']

end C72.T3
