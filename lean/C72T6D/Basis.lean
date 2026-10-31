import C72T6.Search

/-!
# T6, order 2: `Bad(y)` and (diag) on a basis

The paper reads `s_y(B) ∈ Bad(y)` on a basis `x_1, …, x_m` of `Y_y` (Section 3.4), and Lemma 3.3 (c) and the programs
impose (diag) on a basis of `Y`. The Lean conditions ask the equations for every element instead; both readings agree:
* `forall_disjoint_iff_syn`: for words `xs j` of `Y_y` that span `Y_y`, "`⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y_y`" (the
  condition in `BadAt` and `BadAtE`) is "`s_y(B) = (⟨𝟙_e, xs j⟩)_j`";
* `diag_of_span`, `InA0_of_span`: for symmetric `B` on a self-dual `Y`, (diag) on a family that spans `Y` gives (diag)
  for every `y ∈ Y`, because `q(y) = B(y, y) + B(y, 𝟙) + |y|/2` is additive modulo 2 (`half_wt_add_of_selfDual`:
  `|y + y'| = |y| + |y'| - 2|y ∩ y'|`, and `|y ∩ y'|` is even). So `InA0` is the paper's `A_0`.
-/

namespace C72.T6

open C72 C72.T4 Module Finset

variable {ι : Type*} [Fintype ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- **`Bad(y)` on a basis**. -/
theorem forall_disjoint_iff_syn [DecidableEq ι] {m : ℕ} (B : LinearMap.BilinForm (ZMod 2) Y) (y : Y) (e : Finset ι)
    (xs : Fin m → Y) (hdisj : ∀ j i, (y : ι → ZMod 2) i = 0 ∨ (xs j : ι → ZMod 2) i = 0)
    (hspan : ∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) →
      x ∈ Submodule.span (ZMod 2) (Set.range xs)) :
    (∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) →
      indicator e ⬝ᵥ (x : ι → ZMod 2) = B y x) ↔
    syn B y xs = fun j => indicator e ⬝ᵥ (xs j : ι → ZMod 2) := by
  constructor
  · intro h
    funext j
    exact (h (xs j) (hdisj j)).symm
  · intro h x hx
    let f : Y →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun z => indicator e ⬝ᵥ (z : ι → ZMod 2) - B y z
        map_add' := fun a b => by
          simp only [Submodule.coe_add, dotProduct_add, map_add]
          ring
        map_smul' := fun c a => by
          simp only [Submodule.coe_smul, dotProduct_smul, map_smul, smul_eq_mul, RingHom.id_apply]
          ring }
    have hf : ∀ z ∈ Submodule.span (ZMod 2) (Set.range xs), f z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz' =>
        obtain ⟨j, rfl⟩ := hz'
        have hj : B y (xs j) = indicator e ⬝ᵥ (xs j : ι → ZMod 2) := congrFun h j
        show indicator e ⬝ᵥ (xs j : ι → ZMod 2) - B y (xs j) = 0
        rw [hj, sub_self]
      | zero => exact map_zero f
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul c a _ ha => rw [map_smul, ha, smul_zero]
    have h0 : indicator e ⬝ᵥ (x : ι → ZMod 2) - B y x = 0 := hf x (hspan x hx)
    exact sub_eq_zero.1 h0

/-- `|y + y'|/2 = |y|/2 + |y'|/2` modulo 2 for `y, y'` in a self-dual code. -/
theorem half_wt_add_of_selfDual (hY : SelfDual Y) {y y' : ι → ZMod 2} (hy : y ∈ Y) (hy' : y' ∈ Y) :
    ((wt (y + y') / 2 : ℕ) : ZMod 2) = ((wt y / 2 : ℕ) : ZMod 2) + ((wt y' / 2 : ℕ) : ZMod 2) := by
  have key : ∀ a b : ZMod 2, (if a + b ≠ 0 then (1 : ℕ) else 0) +
      2 * ((if a ≠ 0 then (1 : ℕ) else 0) * (if b ≠ 0 then (1 : ℕ) else 0)) =
      (if a ≠ 0 then (1 : ℕ) else 0) + (if b ≠ 0 then (1 : ℕ) else 0) := by decide
  have key2 : ∀ a b : ZMod 2,
      (((if a ≠ 0 then (1 : ℕ) else 0) * (if b ≠ 0 then (1 : ℕ) else 0) : ℕ) : ZMod 2) = a * b := by decide
  have hsum : wt (y + y') + 2 * ∑ i, ((if y i ≠ 0 then (1 : ℕ) else 0) * (if y' i ≠ 0 then (1 : ℕ) else 0)) =
      wt y + wt y' := by
    rw [wt_eq_sum, wt_eq_sum, wt_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => key (y i) (y' i))
  have hcast : ((∑ i, ((if y i ≠ 0 then (1 : ℕ) else 0) * (if y' i ≠ 0 then (1 : ℕ) else 0)) : ℕ) : ZMod 2) =
      y ⬝ᵥ y' := by
    rw [Nat.cast_sum, dotProduct]
    exact Finset.sum_congr rfl (fun i _ => key2 (y i) (y' i))
  rw [dotProduct_eq_zero_of_selfDual hY hy hy'] at hcast
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff_even).1 hcast
  obtain ⟨u, hu⟩ := even_wt_of_mem_selfDual hY hy
  obtain ⟨u', hu'⟩ := even_wt_of_mem_selfDual hY hy'
  have h1 : wt (y + y') / 2 + 2 * t = u + u' := by omega
  have h2 : wt y / 2 = u := by omega
  have h3 : wt y' / 2 = u' := by omega
  have h4 := congrArg (fun n : ℕ => (n : ZMod 2)) h1
  simp only [Nat.cast_add, Nat.cast_mul] at h4
  have h5 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h5, zero_mul, add_zero] at h4
  rw [h2, h3]
  exact h4

/-- **(diag) on a spanning family** (Lemma 3.3 (c) as the paper states it). -/
theorem diag_of_span (hY : SelfDual Y) (h1 : allOnes ∈ Y) (B : LinearMap.BilinForm (ZMod 2) Y)
    (hsym : ∀ y y' : Y, B y y' = B y' y) (s : Set Y) (hs : ∀ y : Y, y ∈ Submodule.span (ZMod 2) s)
    (hdiag : ∀ y ∈ s, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, h1⟩) :
    ∀ y : Y, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, h1⟩ := by
  intro y
  induction hs y using Submodule.span_induction with
  | mem x hx => exact hdiag x hx
  | zero =>
    rw [LinearMap.map_zero₂, LinearMap.map_zero₂, Submodule.coe_zero]
    simp [wt]
  | add a b _ _ ha hb =>
    have e1 : B (a + b) (a + b) = B a a + B a b + (B b a + B b b) := by
      rw [LinearMap.map_add₂, map_add (B a), map_add (B b)]
    have e2 : B (a + b) ⟨allOnes, h1⟩ = B a ⟨allOnes, h1⟩ + B b ⟨allOnes, h1⟩ := LinearMap.map_add₂ B a b _
    rw [e1, e2, Submodule.coe_add,
      half_wt_add_of_selfDual hY a.2 b.2, hsym b a, ha, hb]
    have key : ∀ wa sa q wb sb : ZMod 2, wa + sa + q + (q + (wb + sb)) = wa + wb + (sa + sb) := by decide
    exact key _ _ _ _ _
  | smul c a _ ha =>
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, LinearMap.map_zero₂, LinearMap.map_zero₂, Submodule.coe_zero]
      simp [wt]
    · rw [one_smul]
      exact ha

/-- `InA0` from symmetry and (diag) on a spanning family: `InA0` is the paper's `A_0`. -/
theorem InA0_of_span (hY : SelfDual Y) (h1 : allOnes ∈ Y) (B : LinearMap.BilinForm (ZMod 2) Y)
    (hsym : ∀ y y' : Y, B y y' = B y' y) (s : Set Y) (hs : ∀ y : Y, y ∈ Submodule.span (ZMod 2) s)
    (hdiag : ∀ y ∈ s, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, h1⟩) : InA0 Y h1 B :=
  ⟨hsym, diag_of_span hY h1 B hsym s hs hdiag⟩

end C72.T6
