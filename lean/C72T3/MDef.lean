import C72T3.Psi
import C72T1.Tests

/-!
# T3: the 16 words of `e8` and the function `M` of Sec. 2.3

On one side, the cycles are the points `0, …, 6` of the Fano plane with the lines `{0,1,3}`, `{1,2,4}`,
`{2,3,5}`, `{3,4,6}`, `{4,5,0}`, `{5,6,1}`, `{6,0,2}`, and the words of `e8` are the 16 pairs `(S, x)`:
`(∅, 0)`, `(L, 1)` and `(Lᶜ, 0)` for the seven lines `L`, and `({0, …, 6}, 1)` (`e8Words`). For
`v ∈ 𝔽₁₆⁷` with `w_i = |ψ(v_i)|`,

  `M(v) = min_{(S, x)} (5|S| + x + Σ_{i ∉ S} w_i − Σ_{i ∈ S} w_i)`.

`sideTerm` is the bracket (in `ℕ`; the subtraction does not truncate because `w_i ≤ 4`, see
`sideTerm_eq`), and `M` is its minimum over `e8Words` (`Finset.inf'`).

As words of length 8 (points `0, …, 6`, then the fixed point), the 16 pairs are exactly the code `e8` of
`C72T1.Tests` (`wordVec_mem_e8`, `card_e8Words`), and `sideTerm` is the weight on one side of
`φ₀(S, x) + φ₁(v)` (`sideWt_wordVec`).
-/

namespace C72.T3

open Finset

/-- The seven lines of the Fano plane on the points `0, …, 6` (Sec. 2.2). -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2}}

/-- The 16 words `(S, x)` of `e8` on one side (Sec. 2.2): `(∅, 0)`, `({0, …, 6}, 1)`, and `(L, 1)`, `(Lᶜ, 0)`
for the seven lines `L`. -/
def e8Words : Finset (Finset (Fin 7) × ℕ) :=
  insert (∅, 0) (insert (univ, 1) (fanoLines.image (fun L => (L, 1)) ∪ fanoLines.image (fun L => (Lᶜ, 0))))

theorem card_fanoLines : #fanoLines = 7 := by decide +kernel

theorem card_e8Words : #e8Words = 16 := by decide +kernel

theorem e8Words_nonempty : e8Words.Nonempty :=
  ⟨(∅, 0), mem_insert_self _ _⟩

theorem e8Words_snd_le : ∀ Sx ∈ e8Words, Sx.2 ≤ 1 := by decide +kernel

/-- The expression of Sec. 2.3 for the word `(S, x)`: `5|S| + x + Σ_{i ∉ S} w_i − Σ_{i ∈ S} w_i`. -/
def sideTerm (w : Fin 7 → ℕ) (Sx : Finset (Fin 7) × ℕ) : ℕ :=
  5 * #Sx.1 + Sx.2 + ∑ i ∈ Sx.1ᶜ, w i - ∑ i ∈ Sx.1, w i

/-- `M(v)` (Sec. 2.3): the minimum of `sideTerm` over the 16 words of `e8`, with `w_i = |ψ(v_i)|`. -/
def M (v : Fin 7 → F16) : ℕ :=
  e8Words.inf' e8Words_nonempty (sideTerm fun i => wpsi (v i))

theorem M_le (v : Fin 7 → F16) {Sx : Finset (Fin 7) × ℕ} (h : Sx ∈ e8Words) :
    M v ≤ sideTerm (fun i => wpsi (v i)) Sx :=
  Finset.inf'_le _ h

theorem exists_M_eq (v : Fin 7 → F16) :
    ∃ Sx ∈ e8Words, M v = sideTerm (fun i => wpsi (v i)) Sx :=
  Finset.exists_mem_eq_inf' e8Words_nonempty _

theorem le_M_iff {d : ℕ} (v : Fin 7 → F16) :
    d ≤ M v ↔ ∀ Sx ∈ e8Words, d ≤ sideTerm (fun i => wpsi (v i)) Sx :=
  Finset.le_inf'_iff _ _

/-- The bracket without truncated subtraction: `x + Σ_i (5 − w_i if i ∈ S, w_i if i ∉ S)` when `w_i ≤ 5`. -/
theorem sideTerm_eq (w : Fin 7 → ℕ) (hw : ∀ i, w i ≤ 5) (S : Finset (Fin 7)) (x : ℕ) :
    sideTerm w (S, x) = x + ∑ i, if i ∈ S then 5 - w i else w i := by
  have hsplit : ∑ i, (if i ∈ S then 5 - w i else w i) = ∑ i ∈ S, (5 - w i) + ∑ i ∈ Sᶜ, w i := by
    rw [← Finset.sum_add_sum_compl S]
    congr 1
    · exact Finset.sum_congr rfl (fun i hi => by simp [hi])
    · exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_compl.1 hi])
  have hS : ∑ i ∈ S, (5 - w i) + ∑ i ∈ S, w i = 5 * #S := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hw i)),
      Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsplit]
  show 5 * #S + x + ∑ i ∈ Sᶜ, w i - ∑ i ∈ S, w i = _
  omega

theorem wpsi_zero : wpsi 0 = 0 := by decide +kernel

theorem M_zero : M 0 = 0 := by
  have h := M_le (0 : Fin 7 → F16) (Sx := (∅, 0)) (mem_insert_self _ _)
  have h0 : sideTerm (fun i => wpsi ((0 : Fin 7 → F16) i)) (∅, 0) = 0 := by
    simp [sideTerm, wpsi_zero]
  omega

/-! ## The words as vectors of length 8 -/

/-- The word `(S, x)` as a word of length 8: the indicator of `S` on the points `0, …, 6`, then `x`. -/
def wordVec (Sx : Finset (Fin 7) × ℕ) : Fin 8 → ZMod 2 :=
  fun k => if h : k.val < 7 then (if (⟨k.val, h⟩ : Fin 7) ∈ Sx.1 then 1 else 0) else (Sx.2 : ZMod 2)

/-- Membership in `e8` by the parity checks (`e8` is self-dual). -/
theorem mem_e8_iff_dot {x : Fin 8 → ZMod 2} : x ∈ Tests.e8 ↔ ∀ j, x ⬝ᵥ Tests.e8gen j = 0 := by
  have h : Tests.e8 = dual Tests.e8 := Tests.e8_selfDual
  constructor
  · intro hx j
    rw [h] at hx
    exact (mem_dual.1 hx) _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    rw [h, Tests.e8, mem_dual_span]
    rintro _ ⟨j, rfl⟩
    exact hx j

theorem wordVec_dot : ∀ Sx ∈ e8Words, ∀ j, wordVec Sx ⬝ᵥ Tests.e8gen j = 0 := by decide +kernel

/-- The 16 words lie in `e8`; since they are 16 distinct words and `e8` has 16 elements, they are all of `e8`. -/
theorem wordVec_mem_e8 {Sx : Finset (Fin 7) × ℕ} (h : Sx ∈ e8Words) : wordVec Sx ∈ Tests.e8 :=
  mem_e8_iff_dot.2 (wordVec_dot Sx h)

theorem wordVec_injective : ∀ Sx ∈ e8Words, ∀ Sx' ∈ e8Words, wordVec Sx = wordVec Sx' → Sx = Sx' := by
  decide +kernel

/-- The weight on one side of `φ₀(y) + φ₁(v)`, for a word `y` of length 8 (the points `0, …, 6`, then the
fixed point) and `v ∈ 𝔽₁₆⁷`. -/
def sideWt (y : Fin 8 → ZMod 2) (v : Fin 7 → F16) : ℕ :=
  ∑ i : Fin 7, wt (fun b => y (Fin.castSucc i) + psi (v i) b) + (if y (Fin.last 7) = 0 then 0 else 1)

/-- On a word of `e8`, `sideWt` is the bracket of `M`. -/
theorem sideWt_wordVec {Sx : Finset (Fin 7) × ℕ} (h : Sx ∈ e8Words) (v : Fin 7 → F16) :
    sideWt (wordVec Sx) v = sideTerm (fun i => wpsi (v i)) Sx := by
  obtain ⟨S, x⟩ := Sx
  have hx : x ≤ 1 := e8Words_snd_le _ h
  rw [sideTerm_eq _ (fun i => (wpsi_le (v i)).trans (by norm_num)), sideWt]
  have h1 : ∀ i : Fin 7, wt (fun b => wordVec (S, x) (Fin.castSucc i) + psi (v i) b) =
      if i ∈ S then 5 - wpsi (v i) else wpsi (v i) := by
    intro i
    rw [wt_add_psi]
    by_cases hi : i ∈ S <;> simp [wordVec, hi]
  have h2 : (if wordVec (S, x) (Fin.last 7) = 0 then 0 else 1) = x := by
    interval_cases x <;> simp [wordVec]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), h2, add_comm]

end C72.T3
