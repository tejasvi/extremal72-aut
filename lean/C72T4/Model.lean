import C72T4.Reindex

/-!
# T4: the model of a code with a fixed-point-free involution (Section 3.1 of the paper)

The coordinates are pairs `(i, e)` with `i : ι` and `e : ZMod 2`, and the involution is `aStd (i, e) = (i, e + 1)`
(the paper labels the coordinates `(i, e)` with `1 ≤ i ≤ 36`, `e ∈ 𝔽₂`, so that `a(i, e) = (i, e + 1)`).

* `pv u v` is the word `(u | v)`: `u` on the coordinates `(i, 0)` and `v` on the coordinates `(i, 1)`;
* `Yof C = {u | (u | u) ∈ C}` is the contracted fixed code of `aStd`;
* `sigmaL (u | v) = u + v`;
* `CB Y B` is the code `C_B` of Definition 3.1.

The general duality facts used later (`dual_dual`, `dual_sup`) are proved here for any finite index type.
-/

namespace C72.T4

open C72 Module Finset

/-! ## Duality facts for any finite index type -/

section Duality

variable {K : Type*} {κ : Type*} [Fintype κ]

theorem dual_antitone [CommRing K] {A B : Submodule K (κ → K)} (h : A ≤ B) : dual B ≤ dual A :=
  fun _ hx y hy => hx y (h hy)

theorem le_dual_dual [CommRing K] (W : Submodule K (κ → K)) : W ≤ dual (dual W) := by
  intro w hw x hx
  rw [dotProduct_comm]
  exact hx w hw

theorem dual_dual [Field K] [DecidableEq κ] (W : Submodule K (κ → K)) : dual (dual W) = W := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_dual_dual W)
  have h1 := finrank_add_finrank_dual W
  have h2 := finrank_add_finrank_dual (dual W)
  omega

theorem dual_sup [CommRing K] (A B : Submodule K (κ → K)) : dual (A ⊔ B) = dual A ⊓ dual B := by
  apply le_antisymm
  · exact le_inf (dual_antitone le_sup_left) (dual_antitone le_sup_right)
  · intro x hx y hy
    rw [Submodule.mem_inf] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [dotProduct_add, hx.1 a ha, hx.2 b hb, add_zero]

end Duality

/-! ## Arithmetic in `ZMod 2` -/

theorem zmod2_cases : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by
  decide

theorem zmod2_add_self' : ∀ x : ZMod 2, x + x = 0 := by
  decide

theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ e : ZMod 2, f e = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- `wt x` is the number of nonzero coordinates, written as a sum. -/
theorem wt_eq_sum {κ : Type*} [Fintype κ] (x : κ → ZMod 2) :
    wt x = ∑ i, if x i ≠ 0 then 1 else 0 := by
  unfold wt hammingNorm
  rw [Finset.card_filter]

/-- In `𝔽₂`, `⟨x, x⟩` is the weight of `x` modulo 2. -/
theorem dotProduct_self_eq_wt {κ : Type*} [Fintype κ] (x : κ → ZMod 2) :
    x ⬝ᵥ x = (wt x : ZMod 2) := by
  rw [wt_eq_sum, Nat.cast_sum, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  generalize x i = z
  revert z
  decide

theorem even_wt_of_mem_selfDual {κ : Type*} [Fintype κ] {Y : Submodule (ZMod 2) (κ → ZMod 2)}
    (hY : SelfDual Y) {y : κ → ZMod 2} (hy : y ∈ Y) : Even (wt y) := by
  have h : y ∈ dual Y := by
    rw [← hY]
    exact hy
  have h0 := (mem_dual.1 h) y hy
  rw [dotProduct_self_eq_wt] at h0
  exact (ZMod.natCast_eq_zero_iff_even).1 h0

/-- The all-one word. -/
def allOnes {κ : Type*} : κ → ZMod 2 :=
  fun _ => 1

theorem allOnes_dotProduct {κ : Type*} [Fintype κ] (y : κ → ZMod 2) : allOnes ⬝ᵥ y = (wt y : ZMod 2) := by
  rw [wt_eq_sum, Nat.cast_sum, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [allOnes, one_mul]
  generalize y i = z
  revert z
  decide

/-- A self-dual binary code contains the all-one word. -/
theorem allOnes_mem_of_selfDual {κ : Type*} [Fintype κ] {Y : Submodule (ZMod 2) (κ → ZMod 2)}
    (hY : SelfDual Y) : allOnes ∈ Y := by
  rw [hY]
  intro y hy
  rw [allOnes_dotProduct]
  exact (ZMod.natCast_eq_zero_iff_even).2 (even_wt_of_mem_selfDual hY hy)

variable {ι : Type*}

/-! ## Words on pairs -/

/-- The word `(u | v)`: `u` on the coordinates `(i, 0)` and `v` on the coordinates `(i, 1)`. -/
def pv (u v : ι → ZMod 2) : ι × ZMod 2 → ZMod 2 :=
  fun p => if p.2 = 0 then u p.1 else v p.1

/-- The two halves of a word on pairs. -/
def fstH (c : ι × ZMod 2 → ZMod 2) : ι → ZMod 2 :=
  fun i => c (i, 0)

def sndH (c : ι × ZMod 2 → ZMod 2) : ι → ZMod 2 :=
  fun i => c (i, 1)

@[simp]
theorem pv_apply_zero (u v : ι → ZMod 2) (i : ι) : pv u v (i, 0) = u i :=
  rfl

@[simp]
theorem pv_apply_one (u v : ι → ZMod 2) (i : ι) : pv u v (i, 1) = v i :=
  rfl

@[simp]
theorem fstH_pv (u v : ι → ZMod 2) : fstH (pv u v) = u :=
  rfl

@[simp]
theorem sndH_pv (u v : ι → ZMod 2) : sndH (pv u v) = v :=
  rfl

theorem pv_fstH_sndH (c : ι × ZMod 2 → ZMod 2) : pv (fstH c) (sndH c) = c := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem pv_add (u v u' v' : ι → ZMod 2) : pv u v + pv u' v' = pv (u + u') (v + v') := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem pv_smul (a : ZMod 2) (u v : ι → ZMod 2) : a • pv u v = pv (a • u) (a • v) := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem pv_zero : pv (0 : ι → ZMod 2) 0 = 0 := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem pv_inj {u v u' v' : ι → ZMod 2} (h : pv u v = pv u' v') : u = u' ∧ v = v' :=
  ⟨congrArg fstH h, congrArg sndH h⟩

theorem pv_eq_zero_iff {u v : ι → ZMod 2} : pv u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    rw [← pv_zero] at h
    exact pv_inj h
  · rintro ⟨rfl, rfl⟩
    exact pv_zero

/-- The involution `(i, e) ↦ (i, e + 1)`. -/
def aStd : Equiv.Perm (ι × ZMod 2) :=
  Equiv.prodCongr (Equiv.refl ι) (Equiv.addRight (1 : ZMod 2))

theorem aStd_apply (i : ι) (e : ZMod 2) : aStd (i, e) = (i, e + 1) :=
  rfl

/-- `(u | v) a = (v | u)`. -/
theorem permute_aStd_pv (u v : ι → ZMod 2) : permute aStd (pv u v) = pv v u := by
  funext ⟨i, e⟩
  rcases zmod2_cases e with rfl | rfl <;> rfl

theorem wt_pv [Fintype ι] (u v : ι → ZMod 2) : wt (pv u v) = wt u + wt v := by
  rw [wt_eq_sum, wt_eq_sum, wt_eq_sum, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_zmod2]
  rfl

theorem dotProduct_pv [Fintype ι] (u v u' v' : ι → ZMod 2) :
    pv u v ⬝ᵥ pv u' v' = u ⬝ᵥ u' + v ⬝ᵥ v' := by
  simp only [dotProduct]
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_zmod2]
  rfl

/-! ## The contracted fixed code of `aStd`, the map `σ`, and `C_B` -/

/-- `u ↦ (u | u)`. -/
def diagL : (ι → ZMod 2) →ₗ[ZMod 2] (ι × ZMod 2 → ZMod 2) where
  toFun u := pv u u
  map_add' u u' := (pv_add u u u' u').symm
  map_smul' a u := (pv_smul a u u).symm

/-- `σ (u | v) = u + v`. -/
def sigmaL : (ι × ZMod 2 → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun c := fstH c + sndH c
  map_add' c c' := by
    funext i
    simp only [fstH, sndH, Pi.add_apply]
    abel
  map_smul' a c := by
    funext i
    simp only [fstH, sndH, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem sigmaL_apply (c : ι × ZMod 2 → ZMod 2) : sigmaL c = fstH c + sndH c :=
  rfl

/-- The contracted fixed code `Y = {u | (u | u) ∈ C}` of `aStd`. -/
def Yof (C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  C.comap diagL

theorem mem_Yof {C : Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2)} {u : ι → ZMod 2} : u ∈ Yof C ↔ pv u u ∈ C :=
  Iff.rfl

/-- Definition 3.1: `C_B = {(z | z + y) : y ∈ Y, z with ⟨z, y'⟩ = B(y, y') for all y' ∈ Y}`. -/
def CB [Fintype ι] (Y : Submodule (ZMod 2) (ι → ZMod 2)) (B : LinearMap.BilinForm (ZMod 2) Y) :
    Submodule (ZMod 2) (ι × ZMod 2 → ZMod 2) where
  carrier := {c | ∃ y : Y, ∃ z : ι → ZMod 2, (∀ y' : Y, z ⬝ᵥ (y' : ι → ZMod 2) = B y y') ∧ c = pv z (z + y)}
  add_mem' := by
    rintro c c' ⟨y, z, hz, rfl⟩ ⟨y', z', hz', rfl⟩
    refine ⟨y + y', z + z', fun w => ?_, ?_⟩
    · rw [add_dotProduct, hz w, hz' w, map_add, LinearMap.add_apply]
    · rw [pv_add]
      congr 1
      simp only [Submodule.coe_add]
      abel
  zero_mem' := ⟨0, 0, fun w => by simp, by simp [pv_zero]⟩
  smul_mem' := by
    rintro a c ⟨y, z, hz, rfl⟩
    refine ⟨a • y, a • z, fun w => ?_, ?_⟩
    · rw [smul_dotProduct, hz w, map_smul, LinearMap.smul_apply]
    · rw [pv_smul]
      congr 1
      simp only [Submodule.coe_smul, smul_add]

theorem mem_CB [Fintype ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)} {B : LinearMap.BilinForm (ZMod 2) Y}
    {c : ι × ZMod 2 → ZMod 2} :
    c ∈ CB Y B ↔ ∃ y : Y, ∃ z : ι → ZMod 2, (∀ y' : Y, z ⬝ᵥ (y' : ι → ZMod 2) = B y y') ∧ c = pv z (z + y) :=
  Iff.rfl

/-! ## Lemma 3.3 (a): the weight of `(z | z + y)` -/

/-- Lemma 3.3 (a): `|(z | z + y)| = |y| + 2 |z ∖ supp y|`. -/
theorem wt_pv_add [Fintype ι] (z y : ι → ZMod 2) :
    wt (pv z (z + y)) = wt y + 2 * #(univ.filter (fun i => y i = 0 ∧ z i ≠ 0)) := by
  rw [wt_pv, wt_eq_sum, wt_eq_sum, wt_eq_sum, ← Finset.sum_add_distrib, Finset.card_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  rcases zmod2_cases (z i) with h1 | h1 <;> rcases zmod2_cases (y i) with h2 | h2 <;> simp [h1, h2, zmod2_add_self']

end C72.T4
