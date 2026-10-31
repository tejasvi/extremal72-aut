import C72T6.Converse
import C72T6.Search

/-!
# T6: a toy code for the tests and the controls

`Y4 = {(a, a, b, b)}` is a self-dual code of length 4 that contains `𝟙`. The form `B4(x, x') = x₀x'₂ + x₂x'₀` lies in
`A_0(Y4)`; the form `Bn(x, x') = x₀x'₂` is not symmetric.
-/

namespace C72.T6.Toy

open C72 C72.T4

/-- The code `{(a, a, b, b)}`. -/
def Y4 : Submodule (ZMod 2) (Fin 4 → ZMod 2) where
  carrier := {x | x 0 = x 1 ∧ x 2 = x 3}
  add_mem' := by
    intro x y hx hy
    show (x + y) 0 = (x + y) 1 ∧ (x + y) 2 = (x + y) 3
    rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, hx.1, hx.2, hy.1, hy.2]
    exact ⟨rfl, rfl⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := by
    intro c x hx
    show (c • x) 0 = (c • x) 1 ∧ (c • x) 2 = (c • x) 3
    rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hx.1, hx.2]
    exact ⟨rfl, rfl⟩

theorem mem_Y4 {x : Fin 4 → ZMod 2} : x ∈ Y4 ↔ x 0 = x 1 ∧ x 2 = x 3 :=
  Iff.rfl

theorem dot_four (x y : Fin 4 → ZMod 2) : x ⬝ᵥ y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  rw [dotProduct, Fin.sum_univ_four]

theorem Y4_selfDual : SelfDual Y4 := by
  unfold SelfDual
  apply le_antisymm
  · intro x hx
    rw [mem_dual]
    intro y hy
    rw [dot_four, ← (mem_Y4.1 hx).1, ← (mem_Y4.1 hx).2, ← (mem_Y4.1 hy).1, ← (mem_Y4.1 hy).2]
    have key : ∀ a b : ZMod 2, a + a + b + b = 0 := by decide
    exact key _ _
  · intro x hx
    have h1 := (mem_dual.1 hx) ![1, 1, 0, 0] (mem_Y4.2 ⟨rfl, rfl⟩)
    have h2 := (mem_dual.1 hx) ![0, 0, 1, 1] (mem_Y4.2 ⟨rfl, rfl⟩)
    rw [dot_four] at h1 h2
    simp only [Matrix.cons_val, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact mem_Y4.2 ⟨key _ _ h1, key _ _ h2⟩

theorem allOnes_mem_Y4 : allOnes ∈ Y4 :=
  mem_Y4.2 ⟨rfl, rfl⟩

/-- A word of `Y4` is `(y₀, y₀, y₂, y₂)`. -/
theorem Y4_eq (y : Y4) : (y : Fin 4 → ZMod 2) =
    ![(y : Fin 4 → ZMod 2) 0, (y : Fin 4 → ZMod 2) 0, (y : Fin 4 → ZMod 2) 2, (y : Fin 4 → ZMod 2) 2] := by
  obtain ⟨h01, h23⟩ := mem_Y4.1 y.2
  funext i
  fin_cases i
  · rfl
  · exact h01.symm
  · rfl
  · exact h23.symm

/-- `B4(x, x') = x₀x'₂ + x₂x'₀`. -/
def B4 : LinearMap.BilinForm (ZMod 2) Y4 :=
  LinearMap.mk₂ (ZMod 2)
    (fun x x' => (x : Fin 4 → ZMod 2) 0 * (x' : Fin 4 → ZMod 2) 2 + (x : Fin 4 → ZMod 2) 2 * (x' : Fin 4 → ZMod 2) 0)
    (fun x₁ x₂ x' => by simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun a x x' => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x x₁ x₂ => by simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun a x x' => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)

/-- `Bn(x, x') = x₀x'₂`. -/
def Bn : LinearMap.BilinForm (ZMod 2) Y4 :=
  LinearMap.mk₂ (ZMod 2) (fun x x' => (x : Fin 4 → ZMod 2) 0 * (x' : Fin 4 → ZMod 2) 2)
    (fun x₁ x₂ x' => by simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun a x x' => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x x₁ x₂ => by simp only [Submodule.coe_add, Pi.add_apply]; ring)
    (fun a x x' => by simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring)

/-- `B4 ∈ A_0(Y4)`. -/
theorem B4_InA0 : InA0 Y4 allOnes_mem_Y4 B4 := by
  refine ⟨fun y y' => ?_, fun y => ?_⟩
  · show (y : Fin 4 → ZMod 2) 0 * (y' : Fin 4 → ZMod 2) 2 + (y : Fin 4 → ZMod 2) 2 * (y' : Fin 4 → ZMod 2) 0 =
      (y' : Fin 4 → ZMod 2) 0 * (y : Fin 4 → ZMod 2) 2 + (y' : Fin 4 → ZMod 2) 2 * (y : Fin 4 → ZMod 2) 0
    ring
  · show (y : Fin 4 → ZMod 2) 0 * (y : Fin 4 → ZMod 2) 2 + (y : Fin 4 → ZMod 2) 2 * (y : Fin 4 → ZMod 2) 0 =
      ((wt (y : Fin 4 → ZMod 2) / 2 : ℕ) : ZMod 2) +
        ((y : Fin 4 → ZMod 2) 0 * allOnes 2 + (y : Fin 4 → ZMod 2) 2 * allOnes 0)
    rw [Y4_eq y]
    have key : ∀ a b : ZMod 2, ![a, a, b, b] 0 * ![a, a, b, b] 2 + ![a, a, b, b] 2 * ![a, a, b, b] 0 =
        ((wt ![a, a, b, b] / 2 : ℕ) : ZMod 2) + (![a, a, b, b] 0 * allOnes 2 + ![a, a, b, b] 2 * allOnes 0) := by
      decide
    exact key _ _

end C72.T6.Toy
