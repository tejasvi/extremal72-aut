import C72T4.Lemma32

/-!
# T4: Lemma 3.6, the direction used by Theorem D

Let `Y` be self-dual and `B` a bilinear form on `Y`. If for some `y ∈ Y` a set `e` of coordinates outside `supp y`
satisfies `⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y` disjoint from `y` (the syndrome of `B` at `y` is the pattern of `e`),
then `C_B` contains the word `(z | z + y)` of weight `|y| + 2|e|`, which is nonzero when `y ≠ 0`.

Proof: a word `z₀` with `⟨z₀, y'⟩ = B(y, y')` exists because the functional `B(y, ·)` extends to `𝔽₂^ι`. The word
`𝟙_e + z₀` is orthogonal to `Y_y = Y ∩ (words vanishing on supp y)`, whose dual is `Y + (words supported on supp y)`.
So `z₀ + w` agrees with `𝟙_e` outside `supp y` for some `w ∈ Y`, and Lemma 3.3 (a) gives the weight.
-/

namespace C72.T4

open C72 Module Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The indicator word `𝟙_e` of a set `e` of coordinates. -/
def indicator (e : Finset ι) : ι → ZMod 2 :=
  fun i => if i ∈ e then 1 else 0

/-- The words supported on `supp y`. -/
def suppOn (y : ι → ZMod 2) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | ∀ i, y i = 0 → v i = 0}
  add_mem' := by
    intro v w hv hw i hi
    simp [hv i hi, hw i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro a v hv i hi
    simp [hv i hi]

omit [DecidableEq ι] in
/-- The dual of the words supported on `supp y` is the set of words vanishing on `supp y`. -/
theorem mem_dual_suppOn {y x : ι → ZMod 2} : x ∈ dual (suppOn y) ↔ ∀ i, y i ≠ 0 → x i = 0 := by
  classical
  constructor
  · intro hx i hi
    have hs : (Pi.single i 1 : ι → ZMod 2) ∈ suppOn y := by
      intro j hj
      by_cases hji : j = i
      · subst hji
        exact absurd hj hi
      · simp [hji]
    have := (mem_dual.1 hx) _ hs
    rwa [dotProduct_single, mul_one] at this
  · intro hx v hv
    rw [dotProduct]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases hyi : y i = 0
    · rw [hv i hyi, mul_zero]
    · rw [hx i hyi, zero_mul]

omit [DecidableEq ι] in
/-- Every linear functional on a subspace `Y` is `⟨z, ·⟩` for some word `z`. -/
theorem exists_dotProduct_eq {Y : Submodule (ZMod 2) (ι → ZMod 2)} (f : Y →ₗ[ZMod 2] ZMod 2) :
    ∃ z : ι → ZMod 2, ∀ y' : Y, z ⬝ᵥ (y' : ι → ZMod 2) = f y' := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨(dotProductEquiv (ZMod 2) ι).symm g, fun y' => ?_⟩
  have h1 : dotProductEquiv (ZMod 2) ι ((dotProductEquiv (ZMod 2) ι).symm g) = g :=
    LinearEquiv.apply_symm_apply _ _
  have h2 : (dotProductEquiv (ZMod 2) ι ((dotProductEquiv (ZMod 2) ι).symm g)) (y' : ι → ZMod 2) =
      (dotProductEquiv (ZMod 2) ι).symm g ⬝ᵥ (y' : ι → ZMod 2) := rfl
  rw [← h2, h1]
  exact LinearMap.congr_fun hg y'

/-- **Lemma 3.6 (the direction used).** A syndrome in the bad set gives a word of `C_B` of weight `|y| + 2|e|`. -/
theorem lemma36 {Y : Submodule (ZMod 2) (ι → ZMod 2)} (hY : SelfDual Y) (B : LinearMap.BilinForm (ZMod 2) Y)
    (y : Y) (e : Finset ι) (he : ∀ i ∈ e, (y : ι → ZMod 2) i = 0)
    (hsyn : ∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) →
      indicator e ⬝ᵥ (x : ι → ZMod 2) = B y x) :
    ∃ c ∈ CB Y B, wt c = wt (y : ι → ZMod 2) + 2 * e.card ∧ ((y : ι → ZMod 2) ≠ 0 → c ≠ 0) := by
  obtain ⟨z0, hz0⟩ := exists_dotProduct_eq (B y)
  have hd : indicator e + z0 ∈ dual (Y ⊓ dual (suppOn (y : ι → ZMod 2))) := by
    intro x hx
    rw [Submodule.mem_inf] at hx
    have hdisj : ∀ i, (y : ι → ZMod 2) i = 0 ∨ x i = 0 := by
      intro i
      by_cases hyi : (y : ι → ZMod 2) i = 0
      · exact Or.inl hyi
      · exact Or.inr ((mem_dual_suppOn.1 hx.2) i hyi)
    rw [add_dotProduct, hsyn ⟨x, hx.1⟩ hdisj, hz0 ⟨x, hx.1⟩, zmod2_add_self']
  have hdual : dual (Y ⊓ dual (suppOn (y : ι → ZMod 2))) = Y ⊔ suppOn (y : ι → ZMod 2) := by
    have h1 : Y ⊓ dual (suppOn (y : ι → ZMod 2)) = dual Y ⊓ dual (suppOn (y : ι → ZMod 2)) := by
      rw [← hY]
    rw [h1, ← dual_sup, dual_dual]
  rw [hdual] at hd
  obtain ⟨w, hw, v, hv, hwv⟩ := Submodule.mem_sup.1 hd
  have hzc : ∀ y' : Y, (z0 + w) ⬝ᵥ (y' : ι → ZMod 2) = B y y' := by
    intro y'
    rw [add_dotProduct, hz0, dotProduct_eq_zero_of_selfDual hY hw y'.2, add_zero]
  have hz_out : ∀ i, (y : ι → ZMod 2) i = 0 → (z0 + w) i = indicator e i := by
    intro i hyi
    have hvi : v i = 0 := hv i hyi
    have h := congrFun hwv i
    simp only [Pi.add_apply] at h ⊢
    rw [hvi, add_zero] at h
    rw [h]
    generalize indicator e i = a
    generalize z0 i = b
    revert a b
    decide
  refine ⟨pv (z0 + w) ((z0 + w) + y), mem_CB.2 ⟨y, z0 + w, hzc, rfl⟩, ?_, ?_⟩
  · have hfe : univ.filter (fun i => (y : ι → ZMod 2) i = 0 ∧ (z0 + w) i ≠ 0) = e := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hyi, hzi⟩
        rw [hz_out i hyi] at hzi
        by_contra hie
        exact hzi (by simp [indicator, hie])
      · intro hie
        refine ⟨he i hie, ?_⟩
        rw [hz_out i (he i hie)]
        simp [indicator, hie]
    rw [wt_pv_add, hfe]
  · intro hy0 hc0
    rw [pv_eq_zero_iff] at hc0
    apply hy0
    have h := hc0.2
    rw [hc0.1, zero_add] at h
    exact h

end C72.T4
