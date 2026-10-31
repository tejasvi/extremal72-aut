import C72T4.Codes36

/-!
# T4: the named hypotheses of the order-2 case and the statement of Theorem D

Each named hypothesis is a `def … : Prop`; none is an axiom. The theorems of `C72T4.Main` take them as explicit
premises.

* `H_L2` ((L2), [Nebe12, Thm 3.1]): the contracted fixed code of a fixed-point-free involution of an extremal code is
  a self-dual `[36,18,8]` code.
* `H_L3` ((L3), [AMG08, HM12]): every self-dual `[36,18,8]` code is equivalent to one of the 41 codes `Y_k`.
* `H_D k` (the order-2 search for `Y_k`, Table 3 of the paper): for every form of `A_0(Y_k)`
  some constraint word has its syndrome in the program's bad set.
* `ThmD k` is the paper's Theorem D for `Y_k`.

Lengths and dimensions: a self-dual code is `[n, n/2]` (`SelfDual.two_mul_finrank`), and the contracted fixed code of a
fixed-point-free involution of `Fin 72` has 36 coordinates (`C72T4.Main.card_orbits`).
-/

namespace C72.T4

open C72 Module Finset Equiv

/-- `A_0(Y)`: the symmetric bilinear forms on `Y` that satisfy (diag) `B(y, y) = |y|/2 + B(y, 𝟙)` for every `y ∈ Y`
(Section 6.1 of the paper; here (diag) is required for every `y`). -/
def InA0 {ι : Type*} [Fintype ι] (Y : Submodule (ZMod 2) (ι → ZMod 2)) (h1 : allOnes ∈ Y)
    (B : LinearMap.BilinForm (ZMod 2) Y) : Prop :=
  (∀ y y' : Y, B y y' = B y' y) ∧
    ∀ y : Y, B y y = ((wt (y : ι → ZMod 2) / 2 : ℕ) : ZMod 2) + B y ⟨allOnes, h1⟩

/-- **H_D k** (computation: the order-2 search for `Y_k`). For every form `B ∈ A_0(Y_k)` there is a constraint word
`y ∈ Y_k` of weight 8, 10 or 12 and a set `e` of coordinates outside `supp y` with `2|e| < 16 - |y|` (the program's
patterns `|e| ≤ (16 - |y|)/2 - 1`) such that `⟨𝟙_e, x⟩ = B(y, x)` for every `x ∈ Y_k` disjoint from `y`, i.e. the
syndrome `s_y(B)` lies in the program's bad set. -/
def H_D (k : Fin 41) : Prop :=
  ∀ B : LinearMap.BilinForm (ZMod 2) (Yc k), InA0 (Yc k) (allOnes_mem_Yc k) B →
    ∃ y : Yc k, (wt (y : Fin 36 → ZMod 2) = 8 ∨ wt (y : Fin 36 → ZMod 2) = 10 ∨ wt (y : Fin 36 → ZMod 2) = 12) ∧
      ∃ e : Finset (Fin 36), (∀ i ∈ e, (y : Fin 36 → ZMod 2) i = 0) ∧ 2 * e.card < 16 - wt (y : Fin 36 → ZMod 2) ∧
        ∀ x : Yc k, (∀ i, (y : Fin 36 → ZMod 2) i = 0 ∨ (x : Fin 36 → ZMod 2) i = 0) →
          indicator e ⬝ᵥ (x : Fin 36 → ZMod 2) = B y x

/-- **H_L2** (cited: (L2), [Nebe12, Thm 3.1]). For a fixed-point-free involution `a` of an extremal code `C`, the
contracted fixed code (one coordinate for each cycle of `a`) is self-dual with minimum weight exactly 8, i.e. a
self-dual `[36,18,8]` code. -/
def H_L2 : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → (∀ i, a i ≠ i) →
    SelfDual (contracted a C) ∧ MinWtEq (contracted a C) 8

/-- **H_L3** (cited: (L3), [AMG08, HM12]). Every self-dual code of length 36 with minimum weight exactly 8 is
equivalent to one of the 41 codes `Y_k` of the archive list. Only completeness of the list is used. -/
def H_L3 : Prop :=
  ∀ Y : Code 36, SelfDual Y → MinWtEq Y 8 → ∃ k : Fin 41, PermEquiv Y (Yc k)

/-- **Theorem D** of the paper for `Y_k`: no extremal code has a fixed-point-free involution whose contracted fixed code
is equivalent to `Y_k`. -/
def ThmD (k : Fin 41) : Prop :=
  ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → (∀ i, a i ≠ i) →
    ¬ CodeEquiv (contracted a C) (Yc k)

end C72.T4
