import C72T5.Main
import C72T5.CB48
import C72T2.Tests
import C72T2.G24F4
import C72T3.Tests

/-!
# T5: definition checks on known codes and the content of the named hypotheses

Whether an extremal code of length 72 exists is open, so the hypotheses about extremal codes (`H_primes`, `H_L1`,
`T4.H_L2`, `H_CP5`, `H_CP3`) and the Main Theorem hold trivially if none exists (`hyps_of_no_extremal`). The checks
below show that the definitions are not degenerate:

* `known_codes` collects the checks on known codes made in the other parts and here: `e8` (T1), the Golay code `G24` and
  `G24 ⊗ 𝔽₄`, which meets the premises of `H_LP` and `H_CB` (T2), `e8 ⊕ e8` and `d₁₆⁺` (T3), the 41 codes `Y_k` (T4), the unitary identity matrix, `¬ H_Athr 4` (which uses only
  `M v ≥ 2`) and the seven depth-0 rows of Table 1 in the set `R` at threshold 16 (T3), and the code `E48` of the
  length-48 test with `¬ H_CB48` (T5, `C72T5.CB48`).
* `A0_nonempty`: for every `k` the set `A_0(Y_k)` of `H_D k` is nonempty (the form `B(y, y') = q(y) q(y')` with
  `q(y) = |y|/2 mod 2`, which is additive on a self-dual code), so `H_D k` is not true for an empty reason.
-/

namespace C72.T5

open C72 Matrix

/-! ## `A_0(Y)` is nonempty for a self-dual code `Y` containing the all-one word -/

section A0

variable {κ : Type*} [Fintype κ]

theorem wt_add_add_two_mul (x y : κ → ZMod 2) :
    wt (x + y) + 2 * wt (fun i => x i * y i) = wt x + wt y := by
  rw [T4.wt_eq_sum, T4.wt_eq_sum, T4.wt_eq_sum, T4.wt_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : ∀ a b : ZMod 2, ((if a + b ≠ 0 then 1 else 0) + 2 * (if a * b ≠ 0 then 1 else 0) : ℕ) =
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by decide
  exact key (x i) (y i)

theorem dotProduct_eq_wt_mul (x y : κ → ZMod 2) : x ⬝ᵥ y = (wt (fun i => x i * y i) : ZMod 2) := by
  rw [T4.wt_eq_sum, Nat.cast_sum, dotProduct]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have key : ∀ c : ZMod 2, c = ((if c ≠ 0 then 1 else 0 : ℕ) : ZMod 2) := by decide
  exact key (x i * y i)

/-- On a self-dual binary code, `q(y) = |y|/2 mod 2` is additive. -/
theorem half_wt_add {Y : Submodule (ZMod 2) (κ → ZMod 2)} (hY : SelfDual Y) {y y' : κ → ZMod 2} (hy : y ∈ Y)
    (hy' : y' ∈ Y) :
    ((wt (y + y') / 2 : ℕ) : ZMod 2) = ((wt y / 2 : ℕ) : ZMod 2) + ((wt y' / 2 : ℕ) : ZMod 2) := by
  obtain ⟨a, ha⟩ := T4.even_wt_of_mem_selfDual hY hy
  obtain ⟨b, hb⟩ := T4.even_wt_of_mem_selfDual hY hy'
  have hdot : y ⬝ᵥ y' = 0 := by
    have h : y ∈ dual Y := by
      rw [← hY]
      exact hy
    exact (mem_dual.1 h) y' hy'
  rw [dotProduct_eq_wt_mul] at hdot
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff_even).1 hdot
  have h := wt_add_add_two_mul y y'
  have e1 : wt (y + y') / 2 = a + b - 2 * c := by omega
  have e2 : wt y / 2 = a := by omega
  have e3 : wt y' / 2 = b := by omega
  have e4 : a + b - 2 * c + 2 * c = a + b := by omega
  rw [e1, e2, e3, ← Nat.cast_add]
  have h2c : ((2 * c : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_mul]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  calc ((a + b - 2 * c : ℕ) : ZMod 2) = ((a + b - 2 * c : ℕ) : ZMod 2) + ((2 * c : ℕ) : ZMod 2) := by
        rw [h2c, add_zero]
    _ = ((a + b : ℕ) : ZMod 2) := by rw [← Nat.cast_add, e4]

theorem zmod2_mul_self : ∀ x : ZMod 2, x * x = x := by decide

theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- `q(y) = |y|/2 mod 2` as a linear form on a self-dual code. -/
def halfWt {Y : Submodule (ZMod 2) (κ → ZMod 2)} (hY : SelfDual Y) : Y →ₗ[ZMod 2] ZMod 2 where
  toFun y := ((wt (y : κ → ZMod 2) / 2 : ℕ) : ZMod 2)
  map_add' y y' := half_wt_add hY y.2 y'.2
  map_smul' c y := by
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp [Three.wt_zero]
    · simp

/-- The form `B(y, y') = q(y) q(y')`. -/
def qForm {Y : Submodule (ZMod 2) (κ → ZMod 2)} (hY : SelfDual Y) : LinearMap.BilinForm (ZMod 2) Y :=
  LinearMap.mk₂ (ZMod 2) (fun y y' => halfWt hY y * halfWt hY y')
    (fun y₁ y₂ y' => by rw [map_add, add_mul])
    (fun c y y' => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_assoc])
    (fun y y₁ y₂ => by rw [map_add, mul_add])
    (fun c y y' => by rw [map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm])

theorem wt_allOnes36 : wt (T4.allOnes : Fin 36 → ZMod 2) = 36 := by decide

/-- **`A_0(Y_k)` is nonempty**: the form `q(y) q(y')` is symmetric and satisfies (diag). -/
theorem A0_nonempty (k : Fin 41) : ∃ B : LinearMap.BilinForm (ZMod 2) (T4.Yc k),
    T4.InA0 (T4.Yc k) (T4.allOnes_mem_Yc k) B := by
  refine ⟨qForm (T4.Yc_selfDual k), fun y y' => ?_, fun y => ?_⟩
  · show halfWt _ y * halfWt _ y' = halfWt _ y' * halfWt _ y
    rw [mul_comm]
  · show halfWt _ y * halfWt _ y = ((wt (y : Fin 36 → ZMod 2) / 2 : ℕ) : ZMod 2) +
      halfWt _ y * halfWt _ ⟨T4.allOnes, T4.allOnes_mem_Yc k⟩
    have h1 : halfWt (T4.Yc_selfDual k) ⟨T4.allOnes, T4.allOnes_mem_Yc k⟩ = 0 := by
      show ((wt (T4.allOnes : Fin 36 → ZMod 2) / 2 : ℕ) : ZMod 2) = 0
      rw [wt_allOnes36]
      decide
    rw [h1, mul_zero, add_zero, zmod2_mul_self]
    rfl

end A0

/-! ## The hypotheses about extremal codes hold trivially if no extremal code exists -/

/-- If no extremal code of length 72 exists, the five hypotheses about extremal codes hold for trivial reasons; the
other seven (`T4.H_L3`, `H_16`, `H_Golay`, `H_LP`, `H_A`, `H_CB`, `T4.H_D`) are statements about codes of length 16,
24 and 36, matrices and bilinear forms, which do not depend on that question. -/
theorem hyps_of_no_extremal (h : ¬ ∃ C : Code 72, Ext72 C) :
    H_primes ∧ H_L1 ∧ T4.H_L2 ∧ H_CP5 ∧ H_CP3 :=
  ⟨fun C hC => absurd ⟨C, hC⟩ h, fun C hC => absurd ⟨C, hC⟩ h, fun C hC => absurd ⟨C, hC⟩ h,
    fun C hC => absurd ⟨C, hC⟩ h, fun C hC => absurd ⟨C, hC⟩ h⟩

/-! ## Definition checks on known codes -/

/-- **Definition checks on known codes**, collected from the libraries:
* T1: `e8` is Type II with minimum weight 4 and `Aut e8 ≠ ⊥`;
* T2: the Golay code `G24` is Type II with minimum weight 8, has a word of weight 8, and `Aut G24 ≠ ⊥`;
  `G24 ⊗ 𝔽₄` (`Three.G24F4`) is Hermitian self-dual with minimum weight 8 and has a word of weight 8, so it meets the
  premises of `H_LP` and `H_CB` (`Three.G24F4_antecedent`);
* T3: `e8 ⊕ e8` and `d₁₆⁺` are Type II and not equivalent; the identity matrix is unitary over `𝔽₁₆`; `H_A` with
  threshold 4 is false (this uses only `M v ≥ 2` for `v ≠ 0`); at threshold 16 the seven depth-0 rows of Table 1 lie
  in the set `R` of Sec. 2.5 (`T3.Tests.keyRow_mem_R`);
* T4: the 41 codes `Y_k` are self-dual; T5: `A_0(Y_k)` is nonempty;
* T5: the code `E48` over `𝔽₄` is Hermitian self-dual with minimum weight 6, and the length-48 analog of `H_CB` is
  false. -/
theorem known_codes :
    (TypeII C72.Tests.e8 ∧ MinWt C72.Tests.e8 4 ∧ Aut C72.Tests.e8 ≠ ⊥) ∧
    (TypeII Three.G24 ∧ MinWt Three.G24 8 ∧ (∃ x ∈ Three.G24, wt x = 8) ∧ Aut Three.G24 ≠ ⊥) ∧
    (F4.HSelfDual Three.G24F4 ∧ (∀ e ∈ Three.G24F4, e ≠ 0 → 8 ≤ wt e) ∧ ∃ e ∈ Three.G24F4, wt e = 8) ∧
    (TypeII T3.e8e8 ∧ TypeII T3.d16plus ∧ ¬ PermEquiv T3.e8e8 T3.d16plus) ∧
    ((1 : Matrix (Fin 7) (Fin 7) T3.F16) * (1 : Matrix (Fin 7) (Fin 7) T3.F16)ᴴ = 1 ∧ ¬ H_Athr 4 ∧
      ∀ k : Fin 7, T3.herm (T3.Tests.keyRow k) (T3.Tests.keyRow k) = 1 ∧
        ∀ l : T3.F16, l ≠ 0 → 16 ≤ T3.M (l • T3.Tests.keyRow k) + T3.wpsi l) ∧
    ((∀ k, SelfDual (T4.Yc k)) ∧ ∀ k, ∃ B, T4.InA0 (T4.Yc k) (T4.allOnes_mem_Yc k) B) ∧
    (F4.HSelfDual CB48.E48 ∧ (∀ e ∈ CB48.E48, e ≠ 0 → 6 ≤ wt e) ∧ ¬ H_CB48) :=
  ⟨⟨C72.Tests.e8_check.1, C72.Tests.e8_check.2.1, C72.Tests.Aut_e8_ne_bot⟩,
    Three.Tests.G24_check,
    Three.G24F4_antecedent,
    ⟨T3.e8e8_typeII, T3.d16plus_typeII, T3.Tests.e8e8_not_equiv_d16plus⟩,
    ⟨T3.Tests.one_unitary, T3.Tests.not_H_Athr_four, T3.Tests.keyRow_mem_R⟩,
    ⟨T4.Yc_selfDual, A0_nonempty⟩,
    ⟨CB48.E48_hselfDual, CB48.E48_minWt, not_H_CB48⟩⟩

end C72.T5
