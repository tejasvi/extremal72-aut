import C72T1.Defs

/-!
# T2: supports

`supp x = {i | x i ≠ 0}`, the support of a word over any alphabet with a zero, and the facts about `wt` that
the order-3 modules use. The paper identifies a set of coordinates with its characteristic vector (Section 1,
Conventions); here supports are `Finset`s and `wt x = #(supp x)` (`card_supp`).
-/

namespace C72.Three

open Finset

variable {ι K : Type*} [Fintype ι] [Zero K] [DecidableEq K]

/-- The support `supp x = {i | x i ≠ 0}` of a word `x`. -/
def supp (x : ι → K) : Finset ι :=
  univ.filter (fun i => x i ≠ 0)

theorem mem_supp {x : ι → K} {i : ι} : i ∈ supp x ↔ x i ≠ 0 := by
  simp [supp]

/-- `|x| = #(supp x)`. -/
theorem card_supp (x : ι → K) : #(supp x) = wt x :=
  rfl

theorem wt_zero : wt (0 : ι → K) = 0 :=
  hammingNorm_zero

theorem wt_eq_zero {x : ι → K} : wt x = 0 ↔ x = 0 :=
  hammingNorm_eq_zero

theorem wt_le_card (x : ι → K) : wt x ≤ Fintype.card ι :=
  hammingNorm_le_card_fintype

/-- `|x| = Σᵢ [xᵢ ≠ 0]`. -/
theorem wt_eq_sum (x : ι → K) : wt x = ∑ i, if x i ≠ 0 then 1 else 0 := by
  rw [← card_supp, supp, Finset.card_filter]

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by
  decide

end C72.Three
