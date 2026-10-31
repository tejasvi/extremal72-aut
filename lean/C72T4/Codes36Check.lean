import Mathlib.Data.Nat.Notation
import C72T4.Codes36Data

/-!
# T4: the finite checks on the 41 codes (Bool functions)

`orthoCheck k`: the 18 rows of code `k` are pairwise orthogonal; `pivotCheck k`: every row has a pivot column (a `1`
where all other rows have `0`). Both are evaluated for all 41 codes by `decide +kernel` (kernel evaluation of a closed
Bool term, no `decide` over a bounded quantifier). The module imports only the data, so that changes elsewhere do
not repeat the evaluation. The soundness lemmas are in `C72T4.Codes36`.
-/

namespace C72.T4

/-- `allBelow p n = true` iff `p i = true` for every `i < n`. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

theorem allBelow_spec {p : ℕ → Bool} : ∀ {n : ℕ}, allBelow p n = true → ∀ i < n, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
    · exact allBelow_spec h.1 i hi'
    · exact h.2

/-- `anyBelow p n = true` iff `p i = true` for some `i < n`. -/
def anyBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => anyBelow p n || p n

theorem anyBelow_spec {p : ℕ → Bool} : ∀ {n : ℕ}, anyBelow p n = true → ∃ i < n, p i = true
  | 0, h => by simp [anyBelow] at h
  | n + 1, h => by
    simp only [anyBelow, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, hpi⟩ := anyBelow_spec h
      exact ⟨i, Nat.lt_succ_of_lt hi, hpi⟩
    · exact ⟨n, Nat.lt_succ_self n, h⟩

/-- The parity of the bits `0, …, n - 1` of `m`. -/
def parityUpTo (m : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 => xor (parityUpTo m n) (m.testBit n)

/-- Row `r` of code `k` as a mask (0 out of range). -/
def mask (k r : ℕ) : ℕ :=
  (codesData.getD k []).getD r 0

/-! ## The checks -/

/-- All pairs of the 18 rows `rows 0, …, rows 17` are orthogonal (as 36-bit words). -/
def orthoCheckOn (rows : ℕ → ℕ) : Bool :=
  allBelow (fun r => allBelow (fun s => !parityUpTo (rows r &&& rows s) 36) 18) 18

/-- Every one of the 18 rows has a pivot column: a `1` where all other rows have `0`. -/
def pivotCheckOn (rows : ℕ → ℕ) : Bool :=
  allBelow (fun r => anyBelow (fun p => (rows r).testBit p &&
    allBelow (fun s => s == r || !(rows s).testBit p) 18) 36) 18

/-- All pairs of rows of code `k` are orthogonal. -/
def orthoCheck (k : ℕ) : Bool :=
  orthoCheckOn (mask k)

/-- Every row of code `k` has a pivot column: a `1` where all other rows have `0`. -/
def pivotCheck (k : ℕ) : Bool :=
  pivotCheckOn (mask k)

theorem orthoCheck_all : allBelow orthoCheck 41 = true := by
  decide +kernel

theorem pivotCheck_all : allBelow pivotCheck 41 = true := by
  decide +kernel

end C72.T4
