import C72T4.Lemma36
import C72T4.Codes36Check

/-!
# T4: the 41 codes `Y_k` and their checked properties

`Yc k` is the code spanned by the 18 rows of block `k` of the archive list (`C72T4.Codes36Data`). Two finite checks,
written as Bool-valued recursive functions with soundness lemmas (no `decide` over a bounded quantifier), show for
every `k`:
* the rows are pairwise orthogonal (`orthoCheck`), so `Yc k ⊆ (Yc k)^⊥`;
* each row has a pivot column where it is the only row with a `1` (`pivotCheck`), so the rows are linearly
  independent and `dim Yc k = 18`.
Hence every `Yc k` is self-dual (`Yc_selfDual`) and contains the all-one word (a wrong code list would
make (L3) false; these checks are cheap guards, the minimum weights are not recomputed here).
-/

namespace C72.T4

open C72 Module Finset

theorem sum_bits_eq (m : ℕ) : ∀ n : ℕ,
    (∑ j : Fin n, if m.testBit j then (1 : ZMod 2) else 0) = if parityUpTo m n then 1 else 0
  | 0 => by simp [parityUpTo]
  | n + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [sum_bits_eq m n]
    simp only [parityUpTo]
    rcases Bool.eq_false_or_eq_true (parityUpTo m n) with h | h <;>
      rcases Bool.eq_false_or_eq_true (m.testBit n) with h' | h' <;> simp [h, h', zmod2_add_self']

/-! ## The codes -/

/-- The word of a 36-bit mask: coordinate `j` is bit `j`. -/
def bitvec (m : ℕ) : Fin 36 → ZMod 2 :=
  fun j => if m.testBit j then 1 else 0

/-- The generator rows of `Y_k`. -/
def row (k : Fin 41) (r : Fin 18) : Fin 36 → ZMod 2 :=
  bitvec (mask k r)

/-- The code `Y_k`, `k = 0, …, 40` (numbered as in the paper, Sec. 3.4, in the order of the database). -/
def Yc (k : Fin 41) : Code 36 :=
  Submodule.span (ZMod 2) (Set.range (row k))

theorem bitvec_dotProduct (m m' : ℕ) :
    bitvec m ⬝ᵥ bitvec m' = if parityUpTo (m &&& m') 36 then 1 else 0 := by
  rw [← sum_bits_eq]
  simp only [dotProduct, bitvec]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.testBit_and]
  rcases Bool.eq_false_or_eq_true (m.testBit j) with h | h <;>
    rcases Bool.eq_false_or_eq_true (m'.testBit j) with h' | h' <;> simp [h, h']

/-! ## Soundness -/

theorem row_dotProduct_row (k : Fin 41) (r s : Fin 18) : row k r ⬝ᵥ row k s = 0 := by
  have h := allBelow_spec (allBelow_spec orthoCheck_all k k.2) r r.2
  have h2 := allBelow_spec h s s.2
  rw [Bool.not_eq_true'] at h2
  rw [row, row, bitvec_dotProduct, h2]
  rfl

theorem row_linearIndependent (k : Fin 41) : LinearIndependent (ZMod 2) (row k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg r
  obtain ⟨p, hp, hpiv⟩ := anyBelow_spec (allBelow_spec (allBelow_spec pivotCheck_all k k.2) r r.2)
  rw [Bool.and_eq_true] at hpiv
  have hothers := allBelow_spec hpiv.2
  have hsum := congrFun hg ⟨p, hp⟩
  rw [Finset.sum_apply, Pi.zero_apply] at hsum
  rw [Finset.sum_eq_single r] at hsum
  · simp only [Pi.smul_apply, smul_eq_mul, row, bitvec, hpiv.1, ite_true, mul_one] at hsum
    exact hsum
  · intro s _ hsr
    have hs := hothers s s.2
    have hne : (s : ℕ) ≠ (r : ℕ) := fun h => hsr (Fin.ext h)
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, Bool.not_eq_true'] at hs
    simp only [Pi.smul_apply, smul_eq_mul, row, bitvec, hs]
    simp
  · intro hr
    exact absurd (Finset.mem_univ r) hr

theorem finrank_Yc (k : Fin 41) : finrank (ZMod 2) (Yc k) = 18 := by
  rw [Yc, finrank_span_eq_card (row_linearIndependent k), Fintype.card_fin]

theorem Yc_le_dual (k : Fin 41) : Yc k ≤ dual (Yc k) := by
  rw [Yc, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  rw [SetLike.mem_coe, mem_dual_span]
  rintro _ ⟨s, rfl⟩
  exact row_dotProduct_row k r s

/-- Every `Y_k` is self-dual. -/
theorem Yc_selfDual (k : Fin 41) : SelfDual (Yc k) :=
  selfDual_of_le_of_two_mul_finrank (Yc_le_dual k) (by rw [finrank_Yc, Fintype.card_fin])

theorem allOnes_mem_Yc (k : Fin 41) : allOnes ∈ Yc k :=
  allOnes_mem_of_selfDual (Yc_selfDual k)

end C72.T4
