import C72T3.ThmA

/-!
# T3 tests: definition checks on explicit values

* `M (λ e_i) = |ψ(λ)|` for every unit vector and every `λ` (Sec. 2.5), and `M(0) = 0`.
* `M(v) ≥ 2` for `v ≠ 0` (Sec. 2.3), and hence `H_A` with threshold 4 is false: the identity matrix is unitary
  and `M(a) + M(a·1) ≥ 4` (`not_H_Athr_four`). This uses only the lower bound `M v ≥ 2`; it says nothing about
  `H_A` at threshold 16. With threshold 16 the identity is no counterexample: `M(e₀) + M(e₀·1) = 8`
  (`M_single_add`).
* At threshold 16: the seven depth-0 rows of Table 1 lie in the set `R` of Sec. 2.5 (`keyRow_mem_R`); the unit
  row `(1, …, 1)` does not (control C08).
* The data of `H_16`: `e8 ⊕ e8` and `d₁₆⁺` are Type II (`C72T3.E8`), and they are not equivalent
  (`e8e8_not_equiv_d16plus`): in `d₁₆⁺` two coordinates of different halves lie in a word of weight 4, in
  `e8 ⊕ e8` they do not.
* The Lemma 2.3 check with threshold 12 returns `false` (`C72T3.L23Check.chk12_0`).
-/

namespace C72.T3.Tests

open C72 C72.T3 Matrix Finset

/-- `M(λ e_i) = |ψ(λ)|` (Sec. 2.5). -/
theorem M_single : ∀ (i : Fin 7) (l : F16), M (Pi.single i l) = wpsi l := by decide +kernel

theorem M_zero' : M 0 = 0 :=
  M_zero

theorem e8Words_card_S : ∀ Sx ∈ e8Words, Sx.1 ≠ ∅ → 3 ≤ #Sx.1 := by decide +kernel

theorem wpsi_ge_two : ∀ y : F16, y ≠ 0 → 2 ≤ wpsi y := by decide +kernel

/-- `M(v) ≥ 2` for `v ≠ 0` (Sec. 2.3): the term with `S = ∅` is `Σ_i w_i ≥ 2`, and every other term is at least
`5|S| + x − 4|S| ≥ |S| ≥ 3`. -/
theorem two_le_M (v : Fin 7 → F16) (hv : v ≠ 0) : 2 ≤ M v := by
  rw [le_M_iff]
  rintro ⟨S, x⟩ hSx
  have hw : ∀ i, wpsi (v i) ≤ 5 := fun i => (wpsi_le _).trans (by norm_num)
  rw [sideTerm_eq _ hw]
  by_cases hS : S = ∅
  · subst hS
    obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      exact hv (funext fun i => by
        by_contra hi
        exact h ⟨i, hi⟩)
    have h1 : wpsi (v j) ≤ ∑ i, (if i ∈ (∅ : Finset (Fin 7)) then 5 - wpsi (v i) else wpsi (v i)) := by
      simpa using Finset.single_le_sum (f := fun i => wpsi (v i)) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 := wpsi_ge_two _ hj
    omega
  · have h3 : 3 ≤ #S := e8Words_card_S (S, x) hSx hS
    have h4 : ∑ i : Fin 7, (if i ∈ S then 1 else 0) ≤
        ∑ i, (if i ∈ S then 5 - wpsi (v i) else wpsi (v i)) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ S
      · simp only [hi, ite_true]
        have := wpsi_le (v i)
        omega
      · simp only [hi, ite_false]
        exact Nat.zero_le _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one] at h4
    omega

theorem star_one_zero : star (1 : F16) = 1 ∧ star (0 : F16) = 0 := by decide

/-- The identity matrix is unitary. -/
theorem one_unitary : (1 : Matrix (Fin 7) (Fin 7) F16) * (1 : Matrix (Fin 7) (Fin 7) F16)ᴴ = 1 := by
  have h : (1 : Matrix (Fin 7) (Fin 7) F16)ᴴ = 1 := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [star_one_zero.1]
    · simp [hij, Ne.symm hij, star_one_zero.2]
  rw [h, Matrix.one_mul]

/-- `H_A` with threshold 4 is false: the identity matrix is unitary, and `M(a) + M(a·1) ≥ 4` because `M v ≥ 2` for
`v ≠ 0` (`two_le_M`). This checks only that lower bound; it says nothing about `H_A` at threshold 16. -/
theorem not_H_Athr_four : ¬ H_Athr 4 := by
  intro h
  obtain ⟨a, ha, hlt⟩ := h 1 one_unitary
  rw [Matrix.vecMul_one] at hlt
  have := two_le_M a ha
  omega

/-- With threshold 16 the identity matrix is no counterexample: `M(e₀) + M(e₀ · 1) = 8 < 16`. -/
theorem M_single_add : M (Pi.single 0 1) + M (Pi.single (0 : Fin 7) (1 : F16) ᵥ* 1) = 8 := by
  rw [Matrix.vecMul_one, M_single]
  decide

/-! ## `e8 ⊕ e8` and `d₁₆⁺` are not equivalent -/

theorem e8_wt_values : ∀ Sx ∈ e8Words, wt (wordVec Sx) = 0 ∨ wt (wordVec Sx) = 4 ∨ wt (wordVec Sx) = 8 := by
  decide +kernel

theorem e8_wt_cases {y : Fin 8 → ZMod 2} (hy : y ∈ C72.Tests.e8) : wt y = 0 ∨ wt y = 4 ∨ wt y = 8 := by
  obtain ⟨a, b, c, d, rfl⟩ := C72.Tests.mem_e8_iff.1 hy
  clear hy
  revert a b c d
  decide +kernel

/-- A word of weight 4 of `e8 ⊕ e8` lies in one half. -/
theorem e8e8_w4_half {w : Fin 16 → ZMod 2} (hw : w ∈ e8e8) (h4 : wt w = 4) :
    (fun k : Fin 8 => w (Fin.castAdd 8 k)) = 0 ∨ (fun k : Fin 8 => w (Fin.natAdd 8 k)) = 0 := by
  rw [mem_e8e8] at hw
  rw [wt_eq_halves] at h4
  have h1 := e8_wt_cases hw.1
  have h2 := e8_wt_cases hw.2
  by_cases hz : wt (fun k : Fin 8 => w (Fin.castAdd 8 k)) = 0
  · left
    exact hammingNorm_eq_zero.1 hz
  · right
    have hz2 : wt (fun k : Fin 8 => w (Fin.natAdd 8 k)) = 0 := by omega
    exact hammingNorm_eq_zero.1 hz2

/-- `e8 ⊕ e8` and `d₁₆⁺` are not equivalent, so the two cases of `H_16` are distinct. -/
theorem e8e8_not_equiv_d16plus : ¬ PermEquiv e8e8 d16plus := by
  rintro ⟨p, hp⟩
  have hne : p 0 ≠ p 8 := fun h => absurd (p.injective h) (by decide)
  obtain ⟨w, hw, hw4, hj, hk⟩ := d16plus_pair (p 0) (p 8) hne
  have hu : permute p⁻¹ w ∈ e8e8 := by
    rw [← hp, mem_map_permute_iff] at hw
    exact hw
  have hu4 : wt (permute p⁻¹ w) = 4 := by rw [wt_permute, hw4]
  have h0 : permute p⁻¹ w 0 = 1 := by rw [permute_inv_apply, hj]
  have h8 : permute p⁻¹ w 8 = 1 := by rw [permute_inv_apply, hk]
  rcases e8e8_w4_half hu hu4 with h | h
  · have := congrFun h 0
    simp only [Pi.zero_apply] at this
    have e : (Fin.castAdd 8 (0 : Fin 8) : Fin 16) = 0 := rfl
    rw [e, h0] at this
    exact one_ne_zero this
  · have := congrFun h 0
    simp only [Pi.zero_apply] at this
    have e : (Fin.natAdd 8 (0 : Fin 8) : Fin 16) = 8 := rfl
    rw [e, h8] at this
    exact one_ne_zero this

/-! ## The depth-0 rows of Table 1 lie in `R` (threshold 16) -/

/-- The representative of a norm class (Sec. 2.4): `1`, `1 + t`, `1 + t²` for the classes 1, 2, 3, and `0`. -/
def clsRep (c : ℕ) : F16 :=
  if c = 1 then 1 else if c = 2 then 1 + F16.t else if c = 3 then 1 + F16.t ^ 2 else 0

/-- The patterns `c₀ … c₆` of the keys 0 to 6 of Table 1. -/
def keyPattern : Fin 7 → Fin 7 → ℕ :=
  ![![3, 2, 1, 1, 1, 1, 0], ![3, 2, 2, 2, 1, 1, 0], ![2, 2, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 1, 1, 1],
    ![3, 3, 2, 2, 1, 1, 1], ![3, 1, 3, 2, 2, 1, 1], ![3, 3, 2, 2, 2, 2, 1]]

/-- The row at depth 0 with key `k`: each nonzero entry is the representative of its class (Sec. 2.4). -/
def keyRow (k : Fin 7) : Fin 7 → F16 :=
  fun j => clsRep (keyPattern k j)

/-- **At threshold 16:** each depth-0 row of Table 1 lies in `R` (Sec. 2.5): `⟨u, u⟩ = 1` and
`M(λu) ≥ 16 − |ψ(λ)|` for every `λ ≠ 0`. -/
theorem keyRow_mem_R : ∀ k : Fin 7, herm (keyRow k) (keyRow k) = 1 ∧
    ∀ l : F16, l ≠ 0 → 16 ≤ M (l • keyRow k) + wpsi l := by
  decide +kernel

end C72.T3.Tests
