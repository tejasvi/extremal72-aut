import C72T6K.Klein

/-!
# T6, Klein part: the program's words of weight 14

The Klein program uses one word from each orbit `{y, y β}` of words of weight 8 to 14, with the pattern sets
`{0, …, (16 - |y|)/2 - 1}` (Section 3.6), and the paper notes that the words of weight 14 never remove a child.
`not_badAt_of_wt_14`: for a form of `A_0` a word of weight 14 never has a bad syndrome, since a match would give a word of
`C_B` of weight 14, not divisible by 4. So the program's condition (`IsProgWord`, weights 8 to 14) is `RuledOut`
(`ruledOut_iff_prog`), and the solutions of an instance are the forms the program checks.
-/

namespace C72.T6

open C72 C72.T4 Finset Equiv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Submodule (ZMod 2) (ι → ZMod 2)}

/-- A word of weight 14 never has a bad syndrome for a form of `A_0`: a match would give a word of `C_B` of weight 14. -/
theorem not_badAt_of_wt_14 (hY : SelfDual Y) {h1 : allOnes ∈ Y} {B : LinearMap.BilinForm (ZMod 2) Y}
    (hA : InA0 Y h1 B) {y : Y} (hy : wt (y : ι → ZMod 2) = 14) : ¬ BadAt Y B y := by
  rintro ⟨e, he, hlt, hsyn⟩
  obtain ⟨c, hc, hwc, -⟩ := lemma36 hY B y e he hsyn
  have h4 := CB_doublyEven hY h1 B hA.2 c hc
  rw [hwc, hy] at h4
  rw [hy] at hlt
  omega

/-- The words of the Klein program: weight 8, 10, 12 or 14 (Section 3.6). -/
def IsProgWord (y : ι → ZMod 2) : Prop :=
  wt y = 8 ∨ wt y = 10 ∨ wt y = 12 ∨ wt y = 14

/-- For `B ∈ A(Y, β)` the program's condition (words of weight 8 to 14 from `R`, the larger pattern sets) is
`RuledOut`. -/
theorem ruledOut_iff_prog (hY : SelfDual Y) {h1 : allOnes ∈ Y} (β : Aut Y) (hβ2 : (β : Perm ι) * β = 1)
    {B : LinearMap.BilinForm (ZMod 2) Y} (hB : InA Y h1 β B) (R : Set Y)
    (hR : ∀ y : Y, IsConstraint (y : ι → ZMod 2) → y ∈ R ∨ autLin β y ∈ R) :
    RuledOut Y B ↔ ∃ y ∈ R, IsProgWord (y : ι → ZMod 2) ∧ BadAt Y B y := by
  rw [ruledOut_iff_reps β hβ2 hB.2 R hR]
  constructor
  · rintro ⟨y, hyR, hy, hbad⟩
    unfold IsConstraint at hy
    refine ⟨y, hyR, ?_, hbad⟩
    unfold IsProgWord
    rcases hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rintro ⟨y, hyR, hy, hbad⟩
    unfold IsProgWord at hy
    refine ⟨y, hyR, ?_, hbad⟩
    unfold IsConstraint
    rcases hy with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd hbad (not_badAt_of_wt_14 hY hB.1 h)

end C72.T6
