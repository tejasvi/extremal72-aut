import C72T3.MDef

/-!
# T3: the codes `e8 ⊕ e8` and `d₁₆⁺` of length 16 (data of the named hypothesis `H_16`)

* `e8e8`: the words of length 16 whose first eight and last eight coordinates both lie in the paper's `e8`
  (`C72T1.Tests.e8`: the Fano points `0, …, 6`, then the fixed point). It is Type II (`e8e8_typeII`), and two
  coordinates lie in a common word of weight 4 when they are in the same half (`e8e8_pair`).
* `d16plus`: the span of the seven words `{2i, 2i+1, 2i+2, 2i+3}` (`i = 0, …, 6`), which span `d₁₆`, and the
  glue word `0101…01`. It is Type II (`d16plus_typeII`), and every two coordinates lie in a common word of weight 4
  (`d16plus_pair`).
* `tauP m` (`m : Fin 8`) is the translation of `AG(3, 2)` that swaps `m` and the fixed point 7; it lies in
  `Aut e8` (`tauP_mem_Aut`), so `Aut e8` is transitive on the coordinates.
* `sumPerm σ τ` acts by `σ` on the first half and by `τ` on the second; it lies in `Aut (e8 ⊕ e8)` when
  `σ, τ ∈ Aut e8` (`sumPerm_mem_Aut`).
* `rho` moves the halves to the working layout of Sec. 2.2: the first `e8` on the cycles `0, …, 6` and the fixed
  point 14, the second on the cycles `7, …, 13` and the fixed point 15. `e8e8w` is the image of `e8e8`.
-/

namespace C72.T3

open Equiv Finset

/-! ## `e8 ⊕ e8` -/

/-- `e8 ⊕ e8`: the first eight and the last eight coordinates both lie in `e8`. -/
def e8e8 : Code 16 :=
  Tests.e8.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castAdd 8)) ⊓
    Tests.e8.comap (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.natAdd 8))

theorem mem_e8e8 {x : Fin 16 → ZMod 2} :
    x ∈ e8e8 ↔ (fun k => x (Fin.castAdd 8 k)) ∈ Tests.e8 ∧ (fun k => x (Fin.natAdd 8 k)) ∈ Tests.e8 :=
  Iff.rfl

/-- The word of length 16 with halves `y` and `y'`. -/
def cat (y y' : Fin 8 → ZMod 2) : Fin 16 → ZMod 2 :=
  fun i => if h : i.val < 8 then y ⟨i.val, h⟩ else y' ⟨i.val - 8, by omega⟩

theorem cat_castAdd (y y' : Fin 8 → ZMod 2) (k : Fin 8) : cat y y' (Fin.castAdd 8 k) = y k := by
  simp [cat]

theorem cat_natAdd (y y' : Fin 8 → ZMod 2) (k : Fin 8) : cat y y' (Fin.natAdd 8 k) = y' k := by
  simp [cat]

theorem cat_mem_e8e8 {y y' : Fin 8 → ZMod 2} (hy : y ∈ Tests.e8) (hy' : y' ∈ Tests.e8) :
    cat y y' ∈ e8e8 := by
  rw [mem_e8e8]
  simp only [cat_castAdd, cat_natAdd]
  exact ⟨hy, hy'⟩

theorem sum_fin16_halves {M : Type*} [AddCommMonoid M] (f : Fin 16 → M) :
    ∑ i, f i = ∑ k : Fin 8, f (Fin.castAdd 8 k) + ∑ k : Fin 8, f (Fin.natAdd 8 k) :=
  Fin.sum_univ_add (a := 8) (b := 8) f

theorem e8e8_selfDual : SelfDual e8e8 := by
  have he : Tests.e8 = dual Tests.e8 := Tests.e8_selfDual
  unfold SelfDual
  apply le_antisymm
  · intro x hx
    rw [mem_dual]
    intro y hy
    rw [mem_e8e8] at hx hy
    have h1 : (fun k => x (Fin.castAdd 8 k)) ∈ dual Tests.e8 := by
      rw [← he]
      exact hx.1
    have h2 : (fun k => x (Fin.natAdd 8 k)) ∈ dual Tests.e8 := by
      rw [← he]
      exact hx.2
    have e1 := (mem_dual.1 h1) _ hy.1
    have e2 := (mem_dual.1 h2) _ hy.2
    simp only [dotProduct] at e1 e2 ⊢
    rw [sum_fin16_halves, e1, e2, add_zero]
  · intro y hy
    rw [mem_e8e8, he, mem_dual, mem_dual]
    constructor
    · intro u hu
      have h := (mem_dual.1 hy) (cat u 0) (cat_mem_e8e8 hu (Submodule.zero_mem _))
      simp only [dotProduct] at h ⊢
      rw [sum_fin16_halves] at h
      simp only [cat_castAdd, cat_natAdd, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero] at h
      exact h
    · intro u hu
      have h := (mem_dual.1 hy) (cat 0 u) (cat_mem_e8e8 (Submodule.zero_mem _) hu)
      simp only [dotProduct] at h ⊢
      rw [sum_fin16_halves] at h
      simp only [cat_castAdd, cat_natAdd, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at h
      exact h

theorem wt_eq_halves (x : Fin 16 → ZMod 2) :
    wt x = wt (fun k : Fin 8 => x (Fin.castAdd 8 k)) + wt (fun k : Fin 8 => x (Fin.natAdd 8 k)) := by
  simp only [wt, hammingNorm, Finset.card_filter]
  exact sum_fin16_halves _

theorem wt_zero' {ι : Type*} [Fintype ι] : wt (0 : ι → ZMod 2) = 0 :=
  hammingNorm_zero

theorem e8e8_typeII : TypeII e8e8 := by
  refine ⟨e8e8_selfDual, fun x hx => ?_⟩
  rw [wt_eq_halves]
  exact Nat.dvd_add (Tests.e8_typeII.2 _ hx.1) (Tests.e8_typeII.2 _ hx.2)

/-- Two coordinates of `e8` lie in a common word of weight 4 (one of the 16 words of `e8Words`). -/
theorem e8_pair : ∀ j k : Fin 8, j ≠ k →
    ∃ Sx ∈ e8Words, wt (wordVec Sx) = 4 ∧ wordVec Sx j = 1 ∧ wordVec Sx k = 1 := by
  decide +kernel

/-- In `e8 ⊕ e8`, two coordinates in the same half lie in a common word of weight 4. -/
theorem e8e8_pair (j k : Fin 16) (hjk : j ≠ k) (hsame : j.val < 8 ↔ k.val < 8) :
    ∃ w ∈ e8e8, wt w = 4 ∧ w j = 1 ∧ w k = 1 := by
  by_cases hj : j.val < 8
  · have hk : k.val < 8 := hsame.1 hj
    obtain ⟨Sx, hSx, hw, h1, h2⟩ := e8_pair ⟨j.val, hj⟩ ⟨k.val, hk⟩ (fun h => hjk (Fin.ext (by
      simpa using congrArg Fin.val h)))
    refine ⟨cat (wordVec Sx) 0, cat_mem_e8e8 (wordVec_mem_e8 hSx) (Submodule.zero_mem _), ?_, ?_, ?_⟩
    · rw [wt_eq_halves]
      simp only [cat_castAdd, cat_natAdd, hw, wt_zero', add_zero]
    · simpa [cat, hj] using h1
    · simpa [cat, hk] using h2
  · have hk : ¬ k.val < 8 := fun h => hj (hsame.2 h)
    obtain ⟨Sx, hSx, hw, h1, h2⟩ := e8_pair ⟨j.val - 8, by omega⟩ ⟨k.val - 8, by omega⟩ (fun h => hjk (Fin.ext (by
      have := congrArg Fin.val h
      simp only at this
      omega)))
    refine ⟨cat 0 (wordVec Sx), cat_mem_e8e8 (Submodule.zero_mem _) (wordVec_mem_e8 hSx), ?_, ?_, ?_⟩
    · rw [wt_eq_halves]
      simp only [cat_castAdd, cat_natAdd, hw, wt_zero', zero_add]
    · simpa [cat, hj] using h1
    · simpa [cat, hk] using h2

/-! ## `d₁₆⁺` -/

/-- Generators of `d₁₆⁺`: for `r < 7` the word `{2r, 2r+1, 2r+2, 2r+3}` (these span `d₁₆`), for `r = 7` the
glue word `0101…01`. -/
def d16gen (r : Fin 8) : Fin 16 → ZMod 2 :=
  fun j => if r.val < 7 then (if 2 * r.val ≤ j.val ∧ j.val ≤ 2 * r.val + 3 then 1 else 0)
    else (if j.val % 2 = 1 then 1 else 0)

/-- The code `d₁₆⁺`. -/
def d16plus : Code 16 :=
  Submodule.span (ZMod 2) (Set.range d16gen)

theorem d16gen_dot : ∀ r s : Fin 8, d16gen r ⬝ᵥ d16gen s = 0 := by decide +kernel

theorem d16plus_le_dual : d16plus ≤ dual d16plus := by
  rw [d16plus, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨s, rfl⟩
  exact d16gen_dot r s

theorem d16gen_indep' : ∀ g : Fin 8 → ZMod 2, ∑ i, g i • d16gen i = 0 → g = 0 := by
  decide +kernel

theorem d16gen_linearIndependent : LinearIndependent (ZMod 2) d16gen := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [d16gen_indep' g hg]
  rfl

theorem finrank_d16plus : Module.finrank (ZMod 2) d16plus = 8 := by
  rw [d16plus, finrank_span_eq_card d16gen_linearIndependent, Fintype.card_fin]

theorem d16plus_selfDual : SelfDual d16plus :=
  selfDual_of_le_of_two_mul_finrank d16plus_le_dual (by rw [finrank_d16plus, Fintype.card_fin])

theorem mem_d16plus_iff_dot {x : Fin 16 → ZMod 2} : x ∈ d16plus ↔ ∀ r, x ⬝ᵥ d16gen r = 0 := by
  have h : d16plus = dual d16plus := d16plus_selfDual
  constructor
  · intro hx r
    rw [h] at hx
    exact (mem_dual.1 hx) _ (Submodule.subset_span ⟨r, rfl⟩)
  · intro hx
    rw [h, d16plus, mem_dual_span]
    rintro _ ⟨r, rfl⟩
    exact hx r

theorem d16gen_doublyEven : ∀ a b c d e f g h : ZMod 2,
    4 ∣ wt (a • d16gen 0 + b • d16gen 1 + c • d16gen 2 + d • d16gen 3 + e • d16gen 4 + f • d16gen 5 +
      g • d16gen 6 + h • d16gen 7) := by
  decide +kernel

theorem d16plus_typeII : TypeII d16plus := by
  refine ⟨d16plus_selfDual, fun x hx => ?_⟩
  rw [d16plus, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Fin.sum_univ_eight]
  exact d16gen_doublyEven _ _ _ _ _ _ _ _

/-- The word `{2⌊j/2⌋, 2⌊j/2⌋+1} ∪ {2m, 2m+1}` of weight 4 used for the pair `{j, k}`. -/
def pairD (j k : Fin 16) : Fin 16 → ZMod 2 :=
  let m := if j.val / 2 = k.val / 2 then (j.val / 2 + 1) % 8 else k.val / 2
  fun i => if i.val / 2 = j.val / 2 ∨ i.val / 2 = m then 1 else 0

theorem pairD_spec : ∀ j k : Fin 16, j ≠ k →
    (∀ r, pairD j k ⬝ᵥ d16gen r = 0) ∧ wt (pairD j k) = 4 ∧ pairD j k j = 1 ∧ pairD j k k = 1 := by
  decide +kernel

/-- In `d₁₆⁺`, every two coordinates lie in a common word of weight 4. -/
theorem d16plus_pair (j k : Fin 16) (hjk : j ≠ k) : ∃ w ∈ d16plus, wt w = 4 ∧ w j = 1 ∧ w k = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := pairD_spec j k hjk
  exact ⟨pairD j k, mem_d16plus_iff_dot.2 h1, h2, h3, h4⟩

/-! ## Automorphisms of `e8` and of `e8 ⊕ e8` -/

/-- The coordinates of `e8` as the points of `AG(3, 2)`: the fixed point 7 is the origin and the Fano point `i`
is a nonzero vector, so that the lines are the triples with sum 0. -/
def agVector : Fin 8 → ℕ := ![1, 2, 4, 3, 6, 7, 5, 0]

/-- The inverse of `agVector`. -/
def agPoint : ℕ → Fin 8 := fun v => ![7, 0, 1, 3, 2, 6, 4, 5] ⟨v % 8, Nat.mod_lt _ (by decide)⟩

/-- The translation of `AG(3, 2)` by the vector of `m`: it swaps `m` and the fixed point 7. -/
def tau (m i : Fin 8) : Fin 8 :=
  agPoint (agVector i ^^^ agVector m)

theorem tau_tau : ∀ m i : Fin 8, tau m (tau m i) = i := by decide +kernel

/-- `tau m` as a permutation (an involution). -/
def tauP (m : Fin 8) : Perm (Fin 8) where
  toFun := tau m
  invFun := tau m
  left_inv := tau_tau m
  right_inv := tau_tau m

theorem tauP_apply_self : ∀ m : Fin 8, tauP m m = 7 := by decide +kernel

theorem tauP_gen_dot : ∀ (m : Fin 8) (k l : Fin 4), permute (tauP m) (Tests.e8gen k) ⬝ᵥ Tests.e8gen l = 0 := by
  decide +kernel

/-- The translations are automorphisms of `e8`; hence `Aut e8` is transitive on the coordinates. -/
theorem tauP_mem_Aut (m : Fin 8) : tauP m ∈ Aut Tests.e8 := by
  apply mem_Aut_of_map_le
  rw [Tests.e8, Submodule.map_span_le]
  rintro _ ⟨k, rfl⟩
  exact mem_e8_iff_dot.2 (tauP_gen_dot m k)

/-- `σ` on the first half and `τ` on the second half of `Fin 16`. -/
def sumPerm (σ τ : Perm (Fin 8)) : Perm (Fin (8 + 8)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)

theorem sumPerm_castAdd (σ τ : Perm (Fin 8)) (k : Fin 8) :
    sumPerm σ τ (Fin.castAdd 8 k) = Fin.castAdd 8 (σ k) := by
  rw [sumPerm, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

theorem sumPerm_natAdd (σ τ : Perm (Fin 8)) (k : Fin 8) :
    sumPerm σ τ (Fin.natAdd 8 k) = Fin.natAdd 8 (τ k) := by
  rw [sumPerm, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem sumPerm_symm_castAdd (σ τ : Perm (Fin 8)) (k : Fin 8) :
    (sumPerm σ τ).symm (Fin.castAdd 8 k) = Fin.castAdd 8 (σ.symm k) := by
  rw [Equiv.symm_apply_eq, sumPerm_castAdd, Equiv.apply_symm_apply]

theorem sumPerm_symm_natAdd (σ τ : Perm (Fin 8)) (k : Fin 8) :
    (sumPerm σ τ).symm (Fin.natAdd 8 k) = Fin.natAdd 8 (τ.symm k) := by
  rw [Equiv.symm_apply_eq, sumPerm_natAdd, Equiv.apply_symm_apply]

theorem sumPerm_mem_Aut {σ τ : Perm (Fin 8)} (hσ : σ ∈ Aut Tests.e8) (hτ : τ ∈ Aut Tests.e8) :
    sumPerm σ τ ∈ Aut e8e8 := by
  rw [mem_Aut_iff]
  intro x hx
  rw [mem_e8e8] at hx ⊢
  constructor
  · have h := permute_mem_of_mem_Aut hσ hx.1
    convert h using 1
    funext k
    simp only [permute_apply, sumPerm_symm_castAdd]
  · have h := permute_mem_of_mem_Aut hτ hx.2
    convert h using 1
    funext k
    simp only [permute_apply, sumPerm_symm_natAdd]

/-! ## The working layout -/

/-- From the halves of `e8 ⊕ e8` to the layout of Sec. 2.2: `0, …, 6 ↦ 0, …, 6`, `7 ↦ 14`, `8 + k ↦ 7 + k`
(`k ≤ 6`), `15 ↦ 15`. -/
def rhoFun : Fin 16 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 14, 7, 8, 9, 10, 11, 12, 13, 15]

/-- The inverse of `rhoFun`. -/
def rhoInv : Fin 16 → Fin 16 := ![0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 7, 15]

theorem rho_left : ∀ i, rhoInv (rhoFun i) = i := by decide +kernel
theorem rho_right : ∀ i, rhoFun (rhoInv i) = i := by decide +kernel

/-- The relabelling to the working layout. -/
def rho : Perm (Fin 16) where
  toFun := rhoFun
  invFun := rhoInv
  left_inv := rho_left
  right_inv := rho_right

/-- `e8 ⊕ e8` in the working layout: the first `e8` on the cycles `0, …, 6` and the fixed point 14, the second
on the cycles `7, …, 13` and the fixed point 15. -/
def e8e8w : Code 16 :=
  e8e8.map (permute rho).toLinearMap

theorem mem_map_permute_iff {n : ℕ} {D : Code n} {p : Perm (Fin n)} {x : Fin n → ZMod 2} :
    x ∈ D.map (permute p).toLinearMap ↔ permute p⁻¹ x ∈ D := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show permute p⁻¹ (permute p y) ∈ D
    rw [← permute_mul, inv_mul_cancel, permute_one_apply]
    exact hy
  · intro hx
    refine ⟨permute p⁻¹ x, hx, ?_⟩
    show permute p (permute p⁻¹ x) = x
    rw [← permute_mul, mul_inv_cancel, permute_one_apply]

/-- The coordinates of side A (the first `e8`): the cycles `0, …, 6`, then the fixed point 14. -/
def idxA (k : Fin 8) : Fin 16 := rho (Fin.castAdd 8 k)

/-- The coordinates of side B (the second `e8`): the cycles `7, …, 13`, then the fixed point 15. -/
def idxB (k : Fin 8) : Fin 16 := rho (Fin.natAdd 8 k)

theorem idxA_castSucc : ∀ i : Fin 7, idxA (Fin.castSucc i) = Fin.castAdd 2 (Fin.castAdd 7 i) := by decide +kernel
theorem idxA_last : idxA (Fin.last 7) = Fin.natAdd 14 (0 : Fin 2) := by decide +kernel
theorem idxB_castSucc : ∀ i : Fin 7, idxB (Fin.castSucc i) = Fin.castAdd 2 (Fin.natAdd 7 i) := by decide +kernel
theorem idxB_last : idxB (Fin.last 7) = Fin.natAdd 14 (1 : Fin 2) := by decide +kernel

theorem mem_e8e8w {u : Fin 16 → ZMod 2} :
    u ∈ e8e8w ↔ (fun k => u (idxA k)) ∈ Tests.e8 ∧ (fun k => u (idxB k)) ∈ Tests.e8 := by
  rw [e8e8w, mem_map_permute_iff, mem_e8e8]
  rfl

end C72.T3
