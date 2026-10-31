import C72T6O5.Normal

/-!
# T6 (order 5): tests of the definitions of Sec. 2.4

* The identity matrix is in normal form (`normalForm_one`), while `t · I`, which (a) reaches from it
  (`reach_one_diag_t`), violates (iii): its first scanned entry `t` joins two components and is not the representative
  `1` of its class (`not_NFiii_diag_t`). So (iii) is a real condition: it is not invariant under the symmetries.
* Property (i) is a real condition: it fails for the diagonal matrix `diagM` with entries `1 + t², 1, …, 1`
  (`not_NFi_diagM`).
* The key is not the pattern in general: the row of key 0 of Table 1 read backwards has a smaller key than pattern
  (`key_lt_pattern_revRow`).
* The key uses the Frobenius map: the row `(1 + t², 0, …, 0)` has pattern 3 and key 2, while every image under a
  collineation alone has pattern at least 3 (`key_frobRow`, `collImages_frobRow`).
* The scan processes row 3 before row 2 (`scanIdx_three_two`).

These are the positive sides of the must-fail controls in `C72T6O5Controls/`.
-/

namespace C72.T6O5.Tests

open C72.T3 C72.T6O5 Finset Equiv Matrix

/-! ## The identity matrix is in normal form, `t · I` is not -/

theorem NFiii_one : NFiii (1 : Matrix (Fin 7) (Fin 7) F16) := by
  intro i j hij _
  rw [one_apply] at hij ⊢
  by_cases h : i = j
  · rw [ite_eq_left h]
    decide +kernel
  · exact absurd (ite_eq_right h) hij

theorem key_one_row (i : Fin 7) :
    key ((1 : Matrix (Fin 7) (Fin 7) F16) i) = key ((1 : Matrix (Fin 7) (Fin 7) F16) 0) := by
  obtain ⟨σ, hσ, hσi⟩ := exists_isColl_apply_eq_zero i
  have h : (fun j => (1 : Matrix (Fin 7) (Fin 7) F16) 0 (σ j)) = (1 : Matrix (Fin 7) (Fin 7) F16) i := by
    funext j
    rw [one_apply, one_apply]
    have hiff : (0 = σ j) ↔ (i = j) := by
      constructor
      · intro h0
        exact σ.injective (hσi.trans h0)
      · intro hij
        rw [← hij, hσi]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left (hiff.2 hij)]
    · rw [ite_eq_right hij, ite_eq_right (fun h0 => hij (hiff.1 h0))]
  rw [← h, key_comp hσ]

theorem NFi_one : NFi (1 : Matrix (Fin 7) (Fin 7) F16) := fun i => by
  rw [rowAt_zero, key_one_row i]

theorem NFii_one : NFii (1 : Matrix (Fin 7) (Fin 7) F16) := by
  have h : (fun j => cls ((1 : Matrix (Fin 7) (Fin 7) F16) (rowAt 0) j)) = ![1, 0, 0, 0, 0, 0, 0] := by
    funext j
    revert j
    decide +kernel
  unfold NFii
  rw [key_eq_keyC, pattern_eq_patC, h]
  decide +kernel

/-- The identity matrix is in normal form. -/
theorem normalForm_one : NormalForm (1 : Matrix (Fin 7) (Fin 7) F16) :=
  ⟨NFi_one, NFii_one, NFiii_one⟩

/-- `t · I` is reached from the identity by (a) with `D₁ = I`, `D₂ = t · I`. -/
theorem reach_one_diag_t : Reach 1 (diagonal fun _ => F16.t) := by
  have h := reach_of_step (step_scale (fun _ => (1 : F16)) (fun _ => F16.t) (fun _ => one_pow 5)
    (fun _ => F16.t_pow_five) (1 : Matrix (Fin 7) (Fin 7) F16))
  have e : (diagonal fun _ : Fin 7 => (1 : F16))⁻¹ * 1 * diagonal (fun _ => F16.t) = diagonal fun _ => F16.t := by
    rw [diagonal_one, inv_one, one_mul, one_mul]
  rwa [e] at h

theorem scanIdx_zero_zero : scanIdx 0 0 = 0 := by decide

/-- `t · I` violates (iii): its first scanned entry `t` joins two components (there is no earlier entry) and is not
the representative `1` of its class. -/
theorem not_NFiii_diag_t : ¬ NFiii (diagonal fun _ => F16.t) := by
  intro h
  have hJ : Joins (diagonal fun _ => F16.t) 0 0 := by
    intro hE
    have hiso : ∀ y, ¬ earlierEdge (diagonal fun _ => F16.t) 0 0 (Sum.inl 0) y ∧
        ¬ earlierEdge (diagonal fun _ => F16.t) 0 0 y (Sum.inl 0) := by
      intro y
      constructor
      · rintro ⟨a, b, -, hlt, -, -⟩
        rw [scanIdx_zero_zero] at hlt
        exact Nat.not_lt_zero _ hlt
      · rintro ⟨a, b, -, hlt, -, -⟩
        rw [scanIdx_zero_zero] at hlt
        exact Nat.not_lt_zero _ hlt
    exact Sum.inr_ne_inl ((iff_of_eqvGen_of_isolated hiso _ _ hE).1 rfl)
  have hne : (diagonal fun _ => F16.t) 0 0 ≠ 0 := by
    rw [diagonal_apply_eq]
    decide +kernel
  have h0 := h 0 0 hne hJ
  rw [diagonal_apply_eq] at h0
  exact absurd h0 (by decide +kernel)

/-! ## Property (i) is a real condition -/

/-- The diagonal matrix with entries `1 + t², 1, …, 1`. -/
def diagM : Matrix (Fin 7) (Fin 7) F16 :=
  diagonal ![1 + F16.t ^ 2, 1, 1, 1, 1, 1, 1]

/-- The row at depth 0 of `diagM` has key 2 and row 1 has key 1, so (i) fails. -/
theorem not_NFi_diagM : ¬ NFi diagM := by
  intro h
  have h1 := h 1
  have e0 : (fun j => cls (diagM (rowAt 0) j)) = ![3, 0, 0, 0, 0, 0, 0] := by
    funext j
    revert j
    decide +kernel
  have e1 : (fun j => cls (diagM 1 j)) = ![0, 1, 0, 0, 0, 0, 0] := by
    funext j
    revert j
    decide +kernel
  rw [key_eq_keyC, key_eq_keyC, e0, e1] at h1
  revert h1
  decide +kernel

/-! ## The key is not the pattern in general -/

/-- The depth-0 row of key 0 of Table 1 (pattern `3211110`), read backwards (pattern `0111123`). -/
def revRow : Fin 7 → F16 :=
  fun j => T3.Tests.keyRow 0 (Fin.rev j)

/-- `revRow` is not the smallest pattern in its orbit: a collineation moves its zero entry to column 6. -/
theorem key_lt_pattern_revRow : key revRow < pattern revRow := by
  have h : (fun j => cls (revRow j)) = ![0, 1, 1, 1, 1, 2, 3] := by
    funext j
    revert j
    decide +kernel
  rw [key_eq_keyC, pattern_eq_patC, h]
  decide +kernel

/-! ## The key uses the Frobenius map -/

/-- The row `(1 + t², 0, …, 0)`, one entry of class 3. -/
def frobRow : Fin 7 → F16 :=
  ![1 + F16.t ^ 2, 0, 0, 0, 0, 0, 0]

/-- Its pattern is 3, its key is 2 (the Frobenius map moves class 3 to class 2). -/
theorem key_frobRow : pattern frobRow = 3 ∧ key frobRow = 2 := by
  have h : (fun j => cls (frobRow j)) = ![3, 0, 0, 0, 0, 0, 0] := by
    funext j
    revert j
    decide +kernel
  rw [key_eq_keyC, pattern_eq_patC, h]
  decide +kernel

/-- Every image of `frobRow` under a collineation alone has pattern at least 3. -/
theorem collImages_frobRow : ∀ p ∈ ncTriples, 3 ≤ pattern (img (tableOf p.1 p.2.1 p.2.2) false frobRow) := by
  decide +kernel

/-! ## The scan -/

/-- Row 3 is processed before row 2 (the order is `0, 1, 3, 2, 4, 5, 6`). -/
theorem scanIdx_three_two : scanIdx 3 6 < scanIdx 2 0 := by decide

end C72.T6O5.Tests
