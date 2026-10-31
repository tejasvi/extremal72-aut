import C72T4.Hyps

/-!
# T6: the gauge forms `D_T`, Lemma 6.1 (b), and the bad-syndrome condition

For a self-dual `Y` and `T ⊆` coordinates, `D_T(y, y') = |y ∩ y' ∩ T| mod 2` (Section 3.3 of the paper), and `G_0` is the
span of all `D_T` (Section 6.1). This module proves
* Lemma 3.5 (a), the part about forms: every `D ∈ G_0` is symmetric with `D(y, y) = D(y, 𝟙)`, so `A_0` is a union of
  cosets of `G_0` (`InA0_add`);
* **Lemma 6.1 (b)**: for `D ∈ G_0` and `x` disjoint from `y`, `D(y, x) = 0`; hence the syndrome of `B` at `y` depends only on
  the coset `B + G_0` (`badAt_add_iff`, `ruledOut_add_iff`).

`BadAt Y B y` is the condition of `H_D`: some set `e` outside `supp y` with `2|e| < 16 - |y|` matches the syndrome of `B` at
`y`; `RuledOut Y B` says that this holds for some constraint word (weight 8, 10 or 12). `H_D k` is
`∀ B ∈ A_0(Y_k), RuledOut (Y_k) B` (`H_D_iff`).
-/

namespace C72.T6

open C72 C72.T4 Module Finset

variable {ι : Type*} (Y : Submodule (ZMod 2) (ι → ZMod 2))

/-- `D_T(y, y') = ∑_{i ∈ T} y_i y'_i = |y ∩ y' ∩ T| mod 2`. -/
def DT (T : Finset ι) : LinearMap.BilinForm (ZMod 2) Y :=
  LinearMap.mk₂ (ZMod 2) (fun y y' => ∑ i ∈ T, (y : ι → ZMod 2) i * (y' : ι → ZMod 2) i)
    (fun y₁ y₂ y' => by simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun a y y' => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum])
    (fun y y₁ y₂ => by simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a y y' => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring)

theorem DT_apply (T : Finset ι) (y y' : Y) :
    DT Y T y y' = ∑ i ∈ T, (y : ι → ZMod 2) i * (y' : ι → ZMod 2) i :=
  rfl

/-- `G_0`: the span of the forms `D_T`. -/
def G0 : Submodule (ZMod 2) (LinearMap.BilinForm (ZMod 2) Y) :=
  Submodule.span (ZMod 2) (Set.range (DT Y))

variable {Y}

/-- A property of forms that holds for every `D_T` and is closed under `+`, scalars and `0` holds on `G_0`. -/
theorem G0_induction {P : LinearMap.BilinForm (ZMod 2) Y → Prop} (hT : ∀ T, P (DT Y T)) (h0 : P 0)
    (hadd : ∀ D D', P D → P D' → P (D + D')) (hsmul : ∀ (a : ZMod 2) D, P D → P (a • D)) :
    ∀ D ∈ G0 Y, P D := by
  intro D hD
  induction hD using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    exact hT T
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsmul a x hx

/-- Every `D ∈ G_0` is symmetric. -/
theorem G0_symm : ∀ D ∈ G0 Y, ∀ y y' : Y, D y y' = D y' y := by
  apply G0_induction
  · intro T y y'
    simp only [DT_apply, mul_comm]
  · intro y y'
    rfl
  · intro D D' hD hD' y y'
    simp only [LinearMap.add_apply, hD y y', hD' y y']
  · intro a D hD y y'
    simp only [LinearMap.smul_apply, hD y y']

/-- `D(y, y) = D(y, 𝟙)` for `D ∈ G_0` (Lemma 3.5 (a): `D_T(y, y) = |y ∩ T| = D_T(y, 𝟙)`). -/
theorem G0_diag (h1 : allOnes ∈ Y) : ∀ D ∈ G0 Y, ∀ y : Y, D y y = D y ⟨allOnes, h1⟩ := by
  apply G0_induction
  · intro T y
    simp only [DT_apply, allOnes, mul_one]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    generalize (y : ι → ZMod 2) i = a
    revert a
    decide
  · intro y
    rfl
  · intro D D' hD hD' y
    simp only [LinearMap.add_apply, hD y, hD' y]
  · intro a D hD y
    simp only [LinearMap.smul_apply, hD y]

variable [Fintype ι]

/-- `A_0` is a union of cosets of `G_0`. -/
theorem InA0_add {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y} (hB : InA0 Y h1 B)
    {D : LinearMap.BilinForm (ZMod 2) Y} (hD : D ∈ G0 Y) : InA0 Y h1 (B + D) := by
  refine ⟨fun y y' => ?_, fun y => ?_⟩
  · simp only [LinearMap.add_apply, hB.1 y y', G0_symm D hD y y']
  · simp only [LinearMap.add_apply]
    rw [hB.2 y, G0_diag h1 D hD y, add_assoc]

omit [Fintype ι] in
/-- **Lemma 6.1 (b).** For `D ∈ G_0` and `x` disjoint from `y`, `D(y, x) = 0`. -/
theorem G0_apply_disjoint : ∀ D ∈ G0 Y, ∀ y x : Y,
    (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) → D y x = 0 := by
  apply G0_induction
  · intro T y x hyx
    rw [DT_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rcases hyx i with h | h <;> simp [h]
  · intro y x _
    rfl
  · intro D D' hD hD' y x hyx
    simp only [LinearMap.add_apply, hD y x hyx, hD' y x hyx, add_zero]
  · intro a D hD y x hyx
    simp only [LinearMap.smul_apply, hD y x hyx, smul_zero]

/-! ## The bad-syndrome condition -/

variable [DecidableEq ι]

variable (Y)

/-- `B` has a bad syndrome at `y`: a set `e` of coordinates outside `supp y` with `2|e| < 16 - |y|` and
`⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y` disjoint from `y` (the condition in `H_D`). -/
def BadAt (B : LinearMap.BilinForm (ZMod 2) Y) (y : Y) : Prop :=
  ∃ e : Finset ι, (∀ i ∈ e, (y : ι → ZMod 2) i = 0) ∧ 2 * e.card < 16 - wt (y : ι → ZMod 2) ∧
    ∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) → indicator e ⬝ᵥ (x : ι → ZMod 2) = B y x

/-- A constraint word has weight 8, 10 or 12. -/
def IsConstraint (y : ι → ZMod 2) : Prop :=
  wt y = 8 ∨ wt y = 10 ∨ wt y = 12

/-- `B` is ruled out: some constraint word has a bad syndrome. -/
def RuledOut (B : LinearMap.BilinForm (ZMod 2) Y) : Prop :=
  ∃ y : Y, IsConstraint (y : ι → ZMod 2) ∧ BadAt Y B y

variable {Y}

/-- **Lemma 6.1 (b), for syndromes.** The condition at `y` depends only on the coset `B + G_0`. -/
theorem badAt_add_iff (B : LinearMap.BilinForm (ZMod 2) Y) {D : LinearMap.BilinForm (ZMod 2) Y}
    (hD : D ∈ G0 Y) (y : Y) : BadAt Y (B + D) y ↔ BadAt Y B y := by
  have key : ∀ x : Y, (∀ i, (y : ι → ZMod 2) i = 0 ∨ (x : ι → ZMod 2) i = 0) → (B + D) y x = B y x := by
    intro x hx
    rw [LinearMap.add_apply, LinearMap.add_apply, G0_apply_disjoint D hD y x hx, add_zero]
  constructor
  · rintro ⟨e, he, hcard, hsyn⟩
    exact ⟨e, he, hcard, fun x hx => (hsyn x hx).trans (key x hx)⟩
  · rintro ⟨e, he, hcard, hsyn⟩
    exact ⟨e, he, hcard, fun x hx => (hsyn x hx).trans (key x hx).symm⟩

theorem ruledOut_add_iff (B : LinearMap.BilinForm (ZMod 2) Y) {D : LinearMap.BilinForm (ZMod 2) Y}
    (hD : D ∈ G0 Y) : RuledOut Y (B + D) ↔ RuledOut Y B := by
  constructor
  · rintro ⟨y, hy, hbad⟩
    exact ⟨y, hy, (badAt_add_iff B hD y).1 hbad⟩
  · rintro ⟨y, hy, hbad⟩
    exact ⟨y, hy, (badAt_add_iff B hD y).2 hbad⟩

/-- T4's `H_D k` says exactly: every form of `A_0(Y_k)` is ruled out. -/
theorem H_D_iff (k : Fin 41) :
    H_D k ↔ ∀ B : LinearMap.BilinForm (ZMod 2) (Yc k), InA0 (Yc k) (allOnes_mem_Yc k) B → RuledOut (Yc k) B :=
  Iff.rfl

end C72.T6
