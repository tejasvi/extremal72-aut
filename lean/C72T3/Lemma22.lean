import C72T3.Lemma21

/-!
# T3: Lemma 2.2 (forward direction)

In the layout of Sec. 2.2 (`C₀ = e8e8w`), the cycles `0, …, 6` form side `A` with the fixed point 14 and the cycles
`7, …, 13` form side `B` with the fixed point 15. For `c ∈ 𝔽₁₆¹⁴`, `cA c` and `cB c` are its two halves.

* `wt_sides`: the weight of `φ₀u + φ₁c` is the sum of its weights on the two sides, each given by `sideWt`.
* `lemma22`: if `C` has minimum weight at least 16 and `C₀ = e8e8w`, then `M(c_A) + M(c_B) ≥ 16` for every
  nonzero `c ∈ C₁` (Lemma 2.2, the direction used for Theorem A).
-/

namespace C72.T3

open Equiv Finset

variable {C : Code 72}

/-- The `A`-half of `c ∈ 𝔽₁₆¹⁴`: the cycles `0, …, 6`. -/
def cA (c : Fin 14 → F16) : Fin 7 → F16 :=
  fun i => c (Fin.castAdd 7 i)

/-- The `B`-half of `c ∈ 𝔽₁₆¹⁴`: the cycles `7, …, 13`. -/
def cB (c : Fin 14 → F16) : Fin 7 → F16 :=
  fun i => c (Fin.natAdd 7 i)

theorem sum_fin14 {M : Type*} [AddCommMonoid M] (f : Fin 14 → M) :
    ∑ a, f a = ∑ i : Fin 7, f (Fin.castAdd 7 i) + ∑ i : Fin 7, f (Fin.natAdd 7 i) :=
  Fin.sum_univ_add (a := 7) (b := 7) f

/-- The weight of `φ₀u + φ₁c` is the sum of its weights on the sides `A` and `B`. -/
theorem wt_sides (u : Fin 16 → ZMod 2) (c : Fin 14 → F16) :
    wt (phi0 u + phi1 c) = sideWt (fun k => u (idxA k)) (cA c) + sideWt (fun k => u (idxB k)) (cB c) := by
  rw [wt_phi0_add_phi1, sum_fin14, Fin.sum_univ_two]
  simp only [sideWt, idxA_castSucc, idxA_last, idxB_castSucc, idxB_last, cA, cB]
  omega

theorem cA_ext {c c' : Fin 14 → F16} (hA : cA c = cA c') (hB : cB c = cB c') : c = c' := by
  funext a
  by_cases h : a.val < 7
  · have e : a = Fin.castAdd 7 ⟨a.val, h⟩ := Fin.ext rfl
    rw [e]
    exact congrFun hA ⟨a.val, h⟩
  · have ha := a.isLt
    have e : a = Fin.natAdd 7 (⟨a.val - 7, by omega⟩ : Fin 7) := Fin.ext (by simp only [Fin.val_natAdd]; omega)
    rw [e]
    exact congrFun hB (⟨a.val - 7, by omega⟩ : Fin 7)

/-- **Lemma 2.2 (forward direction).** If `C` has minimum weight at least 16 and `C₀ = e8e8w`, then
`M(c_A) + M(c_B) ≥ 16` for every nonzero `c ∈ C₁`: for the words `(S, x)`, `(S', x')` of `e8` that attain
`M(c_A)` and `M(c_B)`, the word `φ₀(S, x, S', x') + φ₁c` of `C` is nonzero and has weight `M(c_A) + M(c_B)`. -/
theorem lemma22 (hmin : MinWt C 16) (hC0 : C0 C = e8e8w) {hg : g5 ∈ Aut C} {c : Fin 14 → F16}
    (hc : c ∈ C1 C hg) (hne : c ≠ 0) : 16 ≤ M (cA c) + M (cB c) := by
  obtain ⟨SxA, hA, hMA⟩ := exists_M_eq (cA c)
  obtain ⟨SxB, hB, hMB⟩ := exists_M_eq (cB c)
  have hu : permute rho (cat (wordVec SxA) (wordVec SxB)) ∈ C0 C := by
    rw [hC0, e8e8w]
    exact Submodule.mem_map_of_mem (cat_mem_e8e8 (wordVec_mem_e8 hA) (wordVec_mem_e8 hB))
  have huA : (fun k => permute rho (cat (wordVec SxA) (wordVec SxB)) (idxA k)) = wordVec SxA := by
    funext k
    rw [idxA, permute_apply_self, cat_castAdd]
  have huB : (fun k => permute rho (cat (wordVec SxA) (wordVec SxB)) (idxB k)) = wordVec SxB := by
    funext k
    rw [idxB, permute_apply_self, cat_natAdd]
  have hmem : phi0 (permute rho (cat (wordVec SxA) (wordVec SxB))) + phi1 c ∈ C := C.add_mem hu hc
  have hne' : phi0 (permute rho (cat (wordVec SxA) (wordVec SxB))) + phi1 c ≠ 0 :=
    fun h => hne (eq_zero_of_phi0_add_phi1 h)
  have h16 := hmin _ hmem hne'
  rw [wt_sides, huA, huB, sideWt_wordVec hA, sideWt_wordVec hB] at h16
  rw [hMA, hMB]
  exact h16

end C72.T3
