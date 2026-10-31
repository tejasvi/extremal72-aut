import C72T2.Basic
import C72T2.F4

/-!
# T2: Hermitian duality over `𝔽₄`

For words `x, y ∈ 𝔽₄^ι` the Hermitian form is `⟨x, y⟩_H = Σᵢ xᵢ ȳᵢ` with `ȳ = y²` (`hform`). The Hermitian dual
of an `𝔽₄`-linear code `E` is `E^{⊥_H} = {x | ∀ y ∈ E, ⟨x, y⟩_H = 0}` (`hdual`), and `E` is Hermitian self-dual
if `E = E^{⊥_H}` (`HSelfDual`), as in Section 4.1 of the paper ("the code `E` is a Hermitian self-dual
`[24,12]` code"). The weights of a Hermitian self-orthogonal code are even, because
`⟨x, x⟩_H = Σᵢ xᵢ x̄ᵢ ≡ wt(x) (mod 2)` (`hform_self`, `even_wt_of_le_hdual`).
-/

namespace C72.F4

open Finset

variable {ι : Type*} [Fintype ι]

/-- The Hermitian form `⟨x, y⟩_H = Σᵢ xᵢ ȳᵢ`, `ȳ = y²`. -/
def hform (x y : ι → F4) : F4 :=
  ∑ i, x i * star (y i)

theorem hform_add_left (x x' y : ι → F4) : hform (x + x') y = hform x y + hform x' y := by
  simp only [hform, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hform_smul_left (a : F4) (x y : ι → F4) : hform (a • x) y = a * hform x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hform_zero_left (y : ι → F4) : hform 0 y = 0 := by
  simp [hform]

/-- The Hermitian dual `E^{⊥_H} = {x | ∀ y ∈ E, ⟨x, y⟩_H = 0}`. -/
def hdual (E : Submodule F4 (ι → F4)) : Submodule F4 (ι → F4) where
  carrier := {x | ∀ y ∈ E, hform x y = 0}
  zero_mem' := fun y _ => hform_zero_left y
  add_mem' := by
    intro x x' hx hx' y hy
    rw [hform_add_left, hx y hy, hx' y hy, add_zero]
  smul_mem' := by
    intro a x hx y hy
    rw [hform_smul_left, hx y hy, mul_zero]

theorem mem_hdual {E : Submodule F4 (ι → F4)} {x : ι → F4} :
    x ∈ hdual E ↔ ∀ y ∈ E, hform x y = 0 :=
  Iff.rfl

theorem hform_add_right (x y y' : ι → F4) : hform x (y + y') = hform x y + hform x y' := by
  simp only [hform, Pi.add_apply, star_add, mul_add, Finset.sum_add_distrib]

/-- The form is conjugate-linear in its second argument: `⟨x, a y⟩_H = ā ⟨x, y⟩_H`. -/
theorem hform_smul_right (a : F4) (x y : ι → F4) : hform x (a • y) = star a * hform x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The Hermitian dual of a span consists of the words orthogonal to the generators. -/
theorem mem_hdual_span {S : Set (ι → F4)} {x : ι → F4} :
    x ∈ hdual (Submodule.span F4 S) ↔ ∀ y ∈ S, hform x y = 0 := by
  constructor
  · intro h y hy
    exact h y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp only [hform, Pi.zero_apply, star_zero, mul_zero, Finset.sum_const_zero]
    | add y z _ _ hy hz => rw [hform_add_right, hy, hz, add_zero]
    | smul a y _ hy => rw [hform_smul_right, hy, mul_zero]

/-- Hermitian self-dual: `E = E^{⊥_H}`. -/
def HSelfDual (E : Submodule F4 (ι → F4)) : Prop :=
  E = hdual E

/-- `⟨x, x⟩_H = Σᵢ xᵢ x̄ᵢ` is the weight of `x` read in `𝔽₄`. -/
theorem hform_self (x : ι → F4) : hform x x = (wt x : F4) := by
  have h : ∀ i, x i * star (x i) = if x i ≠ 0 then 1 else 0 := fun i => by
    rw [mul_star_self]
    by_cases hx : x i = 0 <;> simp [hx]
  simp only [hform, h]
  rw [Finset.sum_boole]
  rfl

/-- The weights of a Hermitian self-orthogonal code are even. -/
theorem even_wt_of_le_hdual {E : Submodule F4 (ι → F4)} (hE : E ≤ hdual E) {x : ι → F4} (hx : x ∈ E) :
    Even (wt x) := by
  have h := hE hx x hx
  rw [hform_self, natCast_eq] at h
  by_cases h2 : wt x % 2 = 0
  · exact Nat.even_iff.2 h2
  · rw [ite_eq_right h2] at h
    exact absurd h (by decide)

theorem HSelfDual.even_wt {E : Submodule F4 (ι → F4)} (hE : HSelfDual E) {x : ι → F4} (hx : x ∈ E) :
    Even (wt x) :=
  even_wt_of_le_hdual (le_of_eq hE) hx

end C72.F4
