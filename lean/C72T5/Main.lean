import C72T1.Paper
import C72T2.TheoremB
import C72T3.ThmA
import C72T4.Main

/-!
# T5: the Main Theorem from the twelve named hypotheses

**Main Theorem** (paper, Section 1). The automorphism group of a binary doubly-even self-dual `[72,36,16]` code is
trivial.

`C72.mainTheorem` proves it from exactly the twelve named hypotheses below, in this order,
and from nothing else:

| hypothesis | kind | stands for | library |
|---|---|---|---|
| `H_primes` | cited | [Bor15, Thm 6.3] (the list of possible groups), weakened to "only primes 2, 3, 5" | T1 |
| `H_L1` | cited | (L1) [Bou02]: involutions are fixed-point-free | T1 |
| `T4.H_L2` | cited | (L2) [Nebe12, Thm 3.1]: the contracted fixed code is a self-dual `[36,18,8]` code | T4 |
| `T4.H_L3` | cited | (L3) [AMG08, HM12]: the 41 codes are complete | T4 |
| `H_CP5` | cited | [CP82]: an automorphism of order 5 has two fixed points | T3 |
| `H_CP3` | cited | [CP82, Bou04]: an automorphism of order 3 has no fixed point | T2 |
| `H_16` | cited | the doubly-even self-dual codes of length 16 are `e8 ⊕ e8` and `d₁₆⁺` [RS98] | T3 |
| `H_Golay` | cited | uniqueness of the extended Golay code, through [FN12, Lemma 3.1] | T2 |
| `H_LP` | cited | `d ≤ 10` [MOSW78] and no Hermitian self-dual `[24,12,10]` code [LP90] | T2 |
| `H_A` | computation | Proposition 2.4, the order-5 search | T3 |
| `H_CB` | computation | Theorem C (completeness) with the labelling search of Theorem B | T2 |
| `T4.H_D k` | computation | the order-2 search for `Y_k`, `k = 0, …, 40` (Theorem D) | T4 |

The proof assembles the libraries: Theorem A (`thmA_of_hyps`, T3), Theorem B (`thmB_of`, T2), "no fixed-point-free
involution" (`T4.noFPFInv_of`, T4) and T1's final deduction `main_of_cited` (Cauchy's theorem). The theorems `*_def`
below restate every hypothesis and the conclusion as Lean checks them (`Iff.rfl`), so that they can be
quoted exactly.
-/

namespace C72

open Matrix

/-- **Main Theorem** from the twelve named hypotheses:
the automorphism group of a binary doubly-even self-dual `[72,36,16]` code is trivial. -/
theorem mainTheorem (h1 : H_primes) (h2 : H_L1) (h3 : T4.H_L2) (h4 : T4.H_L3) (h5 : H_CP5) (h6 : H_CP3)
    (h7 : H_16) (h8 : H_Golay) (h9 : H_LP) (hA : H_A) (hCB : H_CB) (hD : ∀ k, T4.H_D k) :
    ∀ C : Code 72, Ext72 C → Aut C = ⊥ :=
  main_of_cited h1 h2 (thmA_of_hyps h5 h7 hA) (thmB_of h6 h8 h9 hCB) (T4.noFPFInv_of h3 h4 hD)

/-- The Main Theorem in the paper's own terms (T1's `PaperMain`: `C = C^⊥` written out, dimension 36, doubly-even,
minimum weight exactly 16, and `Aut(C)` the permutations `p` with `Cp = C` for `(xp)_{p(i)} = x_i`). -/
theorem mainTheorem_paper (h1 : H_primes) (h2 : H_L1) (h3 : T4.H_L2) (h4 : T4.H_L3) (h5 : H_CP5) (h6 : H_CP3)
    (h7 : H_16) (h8 : H_Golay) (h9 : H_LP) (hA : H_A) (hCB : H_CB) (hD : ∀ k, T4.H_D k) : PaperMain :=
  paperMain_of_cited h1 h2 (thmA_of_hyps h5 h7 hA) (thmB_of h6 h8 h9 hCB) (T4.noFPFInv_of h3 h4 hD)

/-! ## The hypotheses and the conclusion, as Lean states them -/

theorem H_primes_def : H_primes ↔
    ∀ C : Code 72, Ext72 C → ∀ p : ℕ, p.Prime → p ∣ Nat.card (Aut C) → p = 2 ∨ p = 3 ∨ p = 5 :=
  Iff.rfl

theorem H_L1_def : H_L1 ↔ ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → ∀ i, a i ≠ i :=
  Iff.rfl

theorem H_L2_def : T4.H_L2 ↔ ∀ C : Code 72, Ext72 C → ∀ a ∈ Aut C, orderOf a = 2 → (∀ i, a i ≠ i) →
    SelfDual (contracted a C) ∧ T4.MinWtEq (contracted a C) 8 :=
  Iff.rfl

theorem H_L3_def : T4.H_L3 ↔
    ∀ Y : Code 36, SelfDual Y → T4.MinWtEq Y 8 → ∃ k : Fin 41, PermEquiv Y (T4.Yc k) :=
  Iff.rfl

theorem H_CP5_def : H_CP5 ↔ ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g = 5 →
    (Finset.univ.filter fun i => g i = i).card = 2 :=
  Iff.rfl

theorem H_CP3_def : H_CP3 ↔ ∀ C : Code 72, Ext72 C → ∀ g ∈ Aut C, orderOf g = 3 → ∀ i, g i ≠ i :=
  Iff.rfl

theorem H_16_def : H_16 ↔ ∀ D : Code 16, TypeII D → PermEquiv D T3.e8e8 ∨ PermEquiv D T3.d16plus :=
  Iff.rfl

theorem H_Golay_def : H_Golay ↔ ∀ G : Code 24, TypeII G → MinWt G 8 → PermEquiv G Three.G24 :=
  Iff.rfl

theorem H_LP_def : H_LP ↔ ∀ E : Submodule F4 (Fin 24 → F4), F4.HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) →
    ∃ e ∈ E, wt e = 8 :=
  Iff.rfl

theorem H_A_def : H_A ↔ ∀ U : Matrix (Fin 7) (Fin 7) T3.F16, U * Uᴴ = 1 →
    ∃ a : Fin 7 → T3.F16, a ≠ 0 ∧ T3.M a + T3.M (a ᵥ* U) < 16 :=
  Iff.rfl

theorem H_CB_def : H_CB ↔ ∀ E : Submodule F4 (Fin 24 → F4), F4.HSelfDual E → (∀ e ∈ E, e ≠ 0 → 8 ≤ wt e) →
    (∃ e ∈ E, wt e = 8) → ∀ π : Equiv.Perm (Fin 24),
      (∃ O, Three.IsOctad O ∧ ∃ e ∈ E, (wt e = 8 ∧ 7 ≤ (O.map π.toEmbedding ∩ Three.supp e).card) ∨
          (wt e = 10 ∧ O.map π.toEmbedding ⊆ Three.supp e)) ∨
        ∃ D, Three.IsDodecad D ∧ ∃ e ∈ E, wt e = 12 ∧ Three.supp e = D.map π.toEmbedding :=
  Iff.rfl

theorem H_D_def (k : Fin 41) : T4.H_D k ↔
    ∀ B : LinearMap.BilinForm (ZMod 2) (T4.Yc k), T4.InA0 (T4.Yc k) (T4.allOnes_mem_Yc k) B →
      ∃ y : T4.Yc k, (wt (y : Fin 36 → ZMod 2) = 8 ∨ wt (y : Fin 36 → ZMod 2) = 10 ∨
          wt (y : Fin 36 → ZMod 2) = 12) ∧
        ∃ e : Finset (Fin 36), (∀ i ∈ e, (y : Fin 36 → ZMod 2) i = 0) ∧ 2 * e.card < 16 - wt (y : Fin 36 → ZMod 2) ∧
          ∀ x : T4.Yc k, (∀ i, (y : Fin 36 → ZMod 2) i = 0 ∨ (x : Fin 36 → ZMod 2) i = 0) →
            T4.indicator e ⬝ᵥ (x : Fin 36 → ZMod 2) = B y x :=
  Iff.rfl

/-- The conclusion: `Ext72` and `Aut` are T1's (checked against the paper:
`C72T1.Paper.ext72_iff_paper`, `mem_Aut_iff_paper` prove them equal to the paper's notions). -/
theorem conclusion_def (C : Code 72) : Ext72 C ↔ TypeII C ∧ MinWt C 16 ∧ ∃ x ∈ C, wt x = 16 :=
  Iff.rfl

end C72
